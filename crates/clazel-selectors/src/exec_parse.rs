//! §21.1 "parse a selector": the executable parser.
//!
//! Each function is the spec function of the same name in [`super::spec`], step for step,
//! over the [`ExecItem`]s of a list. Verus checks that it never panics, overflows or loops
//! forever. That it returns what the spec does is **not yet proven**: the contract
//! [`super::contract::parse_selector_ensures`] is stated and unmet, and the WPT parsing
//! cases (`tests/conformance_selectors.rs`) are the evidence for now. What matching needs of
//! its result, well-formed arrays and well-formed selectors, is checked by
//! [`super::exec_check`], which is proven, before [`parse_selector`] returns it.

use super::exec_items::*;
use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_css::parser::exec_declaration::matches_ignoring_case;
use clazel_css::parser::exec_parse::ExecParsed;
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Reading items
// ------------------------------------------------------------------------------------

/// The token at `i`, if it is one, below `hi`.
fn tok(items: &[ExecItem], i: usize, hi: usize) -> (r: Option<&ExecToken>)
    ensures
        r is Some ==> i < hi && i < items.len(),
{
    if i < hi && i < items.len() {
        match item(items, i) {
            ExecItem::Token { token } => Some(token),
            _ => None,
        }
    } else {
        None
    }
}

/// [`is_delim_at`].
fn is_delim(items: &[ExecItem], i: usize, hi: usize, c: u32) -> bool {
    matches!(tok(items, i, hi), Some(ExecToken::Delim { value }) if *value == c)
}

/// The token at `i` is `:`.
fn is_colon(items: &[ExecItem], i: usize, hi: usize) -> bool {
    matches!(tok(items, i, hi), Some(ExecToken::Colon))
}

/// [`ident_at`].
fn ident(items: &[ExecItem], i: usize, hi: usize) -> (r: Option<&Vec<u32>>)
    ensures
        r is Some ==> i < hi && i < items.len(),
{
    match tok(items, i, hi) {
        Some(ExecToken::Ident { value }) => Some(value),
        _ => None,
    }
}

/// [`skip_whitespace`].
fn skip_ws(items: &[ExecItem], i: usize, hi: usize) -> (r: usize)
    ensures
        i <= hi ==> i <= r <= hi,
        i > hi ==> r == i,
{
    let mut j = i;
    while j < hi && matches!(tok(items, j, hi), Some(ExecToken::Whitespace))
        invariant
            i <= j,
            i <= hi ==> j <= hi,
            i > hi ==> j == i,
        decreases hi - j,
    {
        j = j.saturating_add(1);
    }
    j
}

/// [`next_comma`].
fn next_comma_at(items: &[ExecItem], i: usize, hi: usize) -> (r: usize)
    ensures
        i <= hi ==> i <= r <= hi,
        i > hi ==> r == i,
{
    let mut j = i;
    while j < hi && !matches!(tok(items, j, hi), Some(ExecToken::Comma))
        invariant
            i <= j,
            i <= hi ==> j <= hi,
            i > hi ==> j == i,
        decreases hi - j,
    {
        j = j.saturating_add(1);
    }
    j
}

/// What a step of the descent finds ([`Step`]).
pub enum Found<T> {
    /// Nothing of the production starts here.
    Absent,
    /// The production, and the index after it.
    Here(T, usize),
    /// The selector is invalid.
    Invalid,
}

// ------------------------------------------------------------------------------------
// Names
// ------------------------------------------------------------------------------------

/// [`pseudo_class_named`].
fn pseudo_class_of(name: &[u32]) -> Option<PseudoClass> {
    if matches_ignoring_case(name, &[0x6C, 0x69, 0x6E, 0x6B]) {
        Some(PseudoClass::Link)
    } else if matches_ignoring_case(name, &[0x76, 0x69, 0x73, 0x69, 0x74, 0x65, 0x64]) {
        Some(PseudoClass::Visited)
    } else if matches_ignoring_case(name, &[0x61, 0x6E, 0x79, 0x2D, 0x6C, 0x69, 0x6E, 0x6B]) {
        Some(PseudoClass::AnyLink)
    } else if matches_ignoring_case(name, &[0x72, 0x6F, 0x6F, 0x74]) {
        Some(PseudoClass::Root)
    } else if matches_ignoring_case(name, &[0x65, 0x6D, 0x70, 0x74, 0x79]) {
        Some(PseudoClass::Empty)
    } else if matches_ignoring_case(
        name,
        &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
    ) {
        Some(PseudoClass::FirstChild)
    } else if matches_ignoring_case(name, &[0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        Some(PseudoClass::LastChild)
    } else if matches_ignoring_case(name, &[0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        Some(PseudoClass::OnlyChild)
    } else if matches_ignoring_case(
        name,
        &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(PseudoClass::FirstOfType)
    } else if matches_ignoring_case(
        name,
        &[0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(PseudoClass::LastOfType)
    } else if matches_ignoring_case(
        name,
        &[0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(PseudoClass::OnlyOfType)
    } else if matches_ignoring_case(name, &[0x68, 0x6F, 0x76, 0x65, 0x72]) {
        Some(PseudoClass::Hover)
    } else if matches_ignoring_case(name, &[0x61, 0x63, 0x74, 0x69, 0x76, 0x65]) {
        Some(PseudoClass::Active)
    } else if matches_ignoring_case(name, &[0x66, 0x6F, 0x63, 0x75, 0x73]) {
        Some(PseudoClass::Focus)
    } else if matches_ignoring_case(
        name,
        &[0x66, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x76, 0x69, 0x73, 0x69, 0x62, 0x6C, 0x65],
    ) {
        Some(PseudoClass::FocusVisible)
    } else if matches_ignoring_case(
        name,
        &[0x66, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x77, 0x69, 0x74, 0x68, 0x69, 0x6E],
    ) {
        Some(PseudoClass::FocusWithin)
    } else {
        None
    }
}

/// [`pseudo_element_named`].
fn pseudo_element_of(name: &[u32]) -> Option<PseudoElement> {
    if matches_ignoring_case(name, &[0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]) {
        Some(PseudoElement::Before)
    } else if matches_ignoring_case(name, &[0x61, 0x66, 0x74, 0x65, 0x72]) {
        Some(PseudoElement::After)
    } else if matches_ignoring_case(name, &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x69, 0x6E, 0x65]) {
        Some(PseudoElement::FirstLine)
    } else if matches_ignoring_case(
        name,
        &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x65, 0x74, 0x74, 0x65, 0x72],
    ) {
        Some(PseudoElement::FirstLetter)
    } else {
        None
    }
}

/// [`nth_named`].
fn nth_of(name: &[u32]) -> Option<NthKind> {
    if matches_ignoring_case(name, &[0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        Some(NthKind::Child)
    } else if matches_ignoring_case(
        name,
        &[0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
    ) {
        Some(NthKind::LastChild)
    } else if matches_ignoring_case(
        name,
        &[0x6E, 0x74, 0x68, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(NthKind::OfType)
    } else if matches_ignoring_case(
        name,
        &[0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(NthKind::LastOfType)
    } else {
        None
    }
}

/// [`is_user_action`].
fn user_action_class(class: PseudoClass) -> bool {
    matches!(
        class,
        PseudoClass::Hover | PseudoClass::Active | PseudoClass::Focus | PseudoClass::FocusVisible
            | PseudoClass::FocusWithin
    )
}

/// A copy of a code point string.
fn copy(v: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == v@,
{
    let mut out: Vec<u32> = Vec::new();
    out.extend_from_slice(v);
    out
}

// ------------------------------------------------------------------------------------
// The productions without selectors inside
// ------------------------------------------------------------------------------------

/// [`type_selector`].
fn type_selector_at(items: &[ExecItem], i: usize, hi: usize) -> Found<ExecSimple> {
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if let Some(name) = ident(items, i, hi) {
        if is_delim(items, i1, hi, 0x7C) {
            Found::Invalid
        } else {
            Found::Here(ExecSimple::Type { ns: NsPrefix::Absent, name: copy(name) }, i1)
        }
    } else if is_delim(items, i, hi, 0x2A) {
        if is_delim(items, i1, hi, 0x7C) {
            if let Some(name) = ident(items, i2, hi) {
                Found::Here(ExecSimple::Type { ns: NsPrefix::Any, name: copy(name) }, i3)
            } else if is_delim(items, i2, hi, 0x2A) {
                Found::Here(ExecSimple::Universal { ns: NsPrefix::Any }, i3)
            } else {
                Found::Invalid
            }
        } else {
            Found::Here(ExecSimple::Universal { ns: NsPrefix::Absent }, i1)
        }
    } else if is_delim(items, i, hi, 0x7C) {
        if let Some(name) = ident(items, i1, hi) {
            Found::Here(ExecSimple::Type { ns: NsPrefix::NoNamespace, name: copy(name) }, i2)
        } else if is_delim(items, i1, hi, 0x2A) {
            Found::Here(ExecSimple::Universal { ns: NsPrefix::NoNamespace }, i2)
        } else {
            Found::Invalid
        }
    } else {
        Found::Absent
    }
}

/// [`attribute_name`].
fn attribute_name_at(v: &[ExecItem], i: usize) -> Option<(NsPrefix, Vec<u32>, usize)> {
    let hi = v.len();
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if let Some(name) = ident(v, i, hi) {
        if is_delim(v, i1, hi, 0x7C) && ident(v, i2, hi).is_some() {
            None
        } else {
            Some((NsPrefix::Absent, copy(name), i1))
        }
    } else if is_delim(v, i, hi, 0x2A) && is_delim(v, i1, hi, 0x7C) {
        ident(v, i2, hi).map(|name| (NsPrefix::Any, copy(name), i3))
    } else if is_delim(v, i, hi, 0x7C) {
        ident(v, i1, hi).map(|name| (NsPrefix::NoNamespace, copy(name), i2))
    } else {
        None
    }
}

/// [`attr_matcher`].
fn attr_matcher_at(v: &[ExecItem], i: usize) -> Option<(AttrMatcher, usize)> {
    let hi = v.len();
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    if is_delim(v, i, hi, 0x3D) {
        Some((AttrMatcher::Equals, i1))
    } else if is_delim(v, i1, hi, 0x3D) {
        if is_delim(v, i, hi, 0x7E) {
            Some((AttrMatcher::Includes, i2))
        } else if is_delim(v, i, hi, 0x7C) {
            Some((AttrMatcher::DashMatch, i2))
        } else if is_delim(v, i, hi, 0x5E) {
            Some((AttrMatcher::Prefix, i2))
        } else if is_delim(v, i, hi, 0x24) {
            Some((AttrMatcher::Suffix, i2))
        } else if is_delim(v, i, hi, 0x2A) {
            Some((AttrMatcher::Substring, i2))
        } else {
            None
        }
    } else {
        None
    }
}

/// [`attribute_selector`], on the rows `lo` up to `hi` of the `[]` block's value.
fn attribute_selector_of(src: &ExecParsed, lo: usize, hi: usize) -> Option<ExecSimple>
    requires
        src_ok(*src),
{
    let v = read_items(src, lo, hi);
    let v = v.as_slice();
    let end = v.len();
    let (ns, name, after_name) = attribute_name_at(v, skip_ws(v, 0, end))?;
    let at_matcher = skip_ws(v, after_name, end);
    if at_matcher >= end {
        return Some(ExecSimple::Attribute { ns, name, test: None });
    }
    let (matcher, after_matcher) = attr_matcher_at(v, at_matcher)?;
    let at_value = skip_ws(v, after_matcher, end);
    let value = match tok(v, at_value, end) {
        Some(ExecToken::String { value }) => copy(value),
        Some(ExecToken::Ident { value }) => copy(value),
        _ => {
            return None;
        },
    };
    let at_modifier = skip_ws(v, at_value.saturating_add(1), end);
    if at_modifier >= end {
        return Some(
            ExecSimple::Attribute { ns, name, test: Some(ExecAttrTest { matcher, value, flag: None }) },
        );
    }
    let flag = match ident(v, at_modifier, end) {
        Some(m) => if matches_ignoring_case(m, &[0x69]) {
            Some(CaseFlag::I)
        } else if matches_ignoring_case(m, &[0x73]) {
            Some(CaseFlag::S)
        } else {
            None
        },
        None => None,
    };
    if flag.is_some() && skip_ws(v, at_modifier.saturating_add(1), end) >= end {
        Some(ExecSimple::Attribute { ns, name, test: Some(ExecAttrTest { matcher, value, flag }) })
    } else {
        None
    }
}

/// [`pseudo_element`].
fn pseudo_element_at(items: &[ExecItem], i: usize, hi: usize) -> Found<PseudoElement> {
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if !is_colon(items, i, hi) {
        return Found::Absent;
    }
    if is_colon(items, i1, hi) {
        match ident(items, i2, hi) {
            Some(name) => match pseudo_element_of(name) {
                Some(element) => Found::Here(element, i3),
                None => Found::Invalid,
            },
            None => Found::Invalid,
        }
    } else {
        match ident(items, i1, hi) {
            Some(name) => match pseudo_element_of(name) {
                Some(element) => Found::Here(element, i2),
                None => Found::Absent,
            },
            None => Found::Absent,
        }
    }
}

/// [`user_actions`]: the user action pseudo-classes after a pseudo-element, onto `acc`.
fn user_actions_at(items: &[ExecItem], i: usize, hi: usize, acc: &mut Vec<ExecSimple>) -> Option<usize> {
    let mut j = i;
    while j < hi
        invariant
            i <= j,
        decreases hi - j,
    {
        if !is_colon(items, j, hi) {
            return Some(j);
        }
        let class = pseudo_class_of(ident(items, j.saturating_add(1), hi)?)?;
        if !user_action_class(class) {
            return None;
        }
        acc.push(ExecSimple::PseudoClass { class });
        j = j.checked_add(2)?;
    }
    Some(j)
}

/// [`pseudo_compound`].
fn pseudo_compound_at(
    items: &[ExecItem],
    i: usize,
    hi: usize,
    acc: &mut Vec<ExecSimple>,
    no_pseudo: bool,
) -> Option<usize> {
    match pseudo_element_at(items, i, hi) {
        Found::Absent => Some(i),
        Found::Invalid => None,
        Found::Here(element, next) => {
            if no_pseudo {
                return None;
            }
            acc.push(ExecSimple::PseudoElement { element });
            user_actions_at(items, next, hi, acc)
        },
    }
}

/// [`has_pseudo_element`].
fn holds_pseudo_element(compound: &[ExecSimple]) -> bool {
    let mut k = 0;
    while k < compound.len()
        decreases compound.len() - k,
    {
        if matches!(item(compound, k), ExecSimple::PseudoElement { .. }) {
            return true;
        }
        k = k.saturating_add(1);
    }
    false
}

/// [`combinator_at`].
fn combinator_of(items: &[ExecItem], i: usize, hi: usize) -> Option<Combinator> {
    if is_delim(items, i, hi, 0x3E) {
        Some(Combinator::Child)
    } else if is_delim(items, i, hi, 0x2B) {
        Some(Combinator::NextSibling)
    } else if is_delim(items, i, hi, 0x7E) {
        Some(Combinator::SubsequentSibling)
    } else {
        None
    }
}

// ------------------------------------------------------------------------------------
// <an+b> (CSS Syntax §6.2), on items
// ------------------------------------------------------------------------------------

/// The value of a number's sign and digits, clamped to the 32-bit range ([`clamp`]): CSS
/// Syntax's "integer value" of an integer token, which has no point and no exponent.
fn clamped_value(number: &ExecNumber) -> i32 {
    let part = number.number_part.as_slice();
    let mut k = 0;
    let mut negative = false;
    if !part.is_empty() && (*item(part, 0) == 0x2B || *item(part, 0) == 0x2D) {
        negative = *item(part, 0) == 0x2D;
        k = 1;
    }
    let mut magnitude: u64 = 0;
    while k < part.len()
        decreases part.len() - k,
    {
        let c = *item(part, k);
        if (0x30..=0x39).contains(&c) && magnitude <= 0x1_0000_0000 {
            magnitude = magnitude.saturating_mul(10).saturating_add((c.saturating_sub(0x30)) as u64);
        }
        k = k.saturating_add(1);
    }
    signed(negative, magnitude)
}

/// `-b`, clamped.
fn negate(b: i32) -> i32 {
    0i32.checked_sub(b).unwrap_or(i32::MAX)
}

/// `magnitude`, negated if `negative`, clamped.
fn signed(negative: bool, magnitude: u64) -> i32 {
    if negative {
        if magnitude >= 0x8000_0000 {
            i32::MIN
        } else {
            negate(magnitude as i32)
        }
    } else if magnitude >= 0x7FFF_FFFF {
        i32::MAX
    } else {
        magnitude as i32
    }
}

/// The digits from `start` of `s` as a negative number, clamped: [`negative_remainder`].
fn remainder(s: &[u32], start: usize) -> i32 {
    let mut k = start.saturating_add(1);
    let mut magnitude: u64 = 0;
    while k < s.len()
        decreases s.len() - k,
    {
        let c = *item(s, k);
        if magnitude <= 0x1_0000_0000 {
            magnitude = magnitude.saturating_mul(10).saturating_add((c.saturating_sub(0x30)) as u64);
        }
        k = k.saturating_add(1);
    }
    signed(true, magnitude)
}

/// [`is_n_dash_digits`].
fn n_dash_digits(s: &[u32], start: usize) -> bool {
    if start >= s.len() || s.len().saturating_sub(start) < 3 {
        return false;
    }
    if clazel_css::parser::exec_declaration::lowercase(*item(s, start)) != 0x6E || *item(
        s,
        start.saturating_add(1),
    ) != 0x2D {
        return false;
    }
    let mut k = start.saturating_add(2);
    while k < s.len()
        decreases s.len() - k,
    {
        if !(0x30..=0x39).contains(item(s, k)) {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// The token of an item that is one.
fn token_of(it: &ExecItem) -> Option<&ExecToken> {
    match it {
        ExecItem::Token { token } => Some(token),
        _ => None,
    }
}

/// The item at `i` of a list of item references.
fn at<'a>(items: &[&'a ExecItem], i: usize) -> &'a ExecItem
    requires
        i < items@.len(),
{
    match items.get(i) {
        Some(x) => x,
        None => vstd::pervasive::unreached(),
    }
}

/// [`is_keyword`].
fn keyword(it: &ExecItem, lowercase: &[u32]) -> bool {
    matches!(token_of(it), Some(ExecToken::Ident { value }) if matches_ignoring_case(value, lowercase))
}

/// [`is_plus`] and [`is_minus`].
fn delim_item(it: &ExecItem, c: u32) -> bool {
    matches!(token_of(it), Some(ExecToken::Delim { value }) if *value == c)
}

/// [`integer_number`].
fn integer_of(it: &ExecItem) -> Option<&ExecNumber> {
    match token_of(it) {
        Some(ExecToken::Number { number }) if number.is_integer => Some(number),
        _ => None,
    }
}

/// [`signed_integer`].
fn signed_of(it: &ExecItem) -> Option<i32> {
    match integer_of(it) {
        Some(number) if number.sign_character.is_some() => Some(clamped_value(number)),
        _ => None,
    }
}

/// [`signless_integer`].
fn signless_of(it: &ExecItem) -> Option<i32> {
    match integer_of(it) {
        Some(number) if number.sign_character.is_none() => Some(clamped_value(number)),
        _ => None,
    }
}

/// An integer dimension: its value and unit.
fn integer_dimension(it: &ExecItem) -> Option<(i32, &Vec<u32>)> {
    match token_of(it) {
        Some(ExecToken::Dimension { number, unit }) if number.is_integer => Some(
            (clamped_value(number), unit),
        ),
        _ => None,
    }
}

/// [`a_of_n`] (`dash` false) or [`a_of_n_dash`] (`dash` true): (A, items taken).
fn a_of(items: &[&ExecItem], plus_adjacent: bool, dash: bool) -> Option<(i32, usize)> {
    if items.is_empty() {
        return None;
    }
    let first = at(items, 0);
    let (n, dash_n): (&[u32], &[u32]) = if dash {
        (&[0x6E, 0x2D], &[0x2D, 0x6E, 0x2D])
    } else {
        (&[0x6E], &[0x2D, 0x6E])
    };
    match integer_dimension(first) {
        Some((value, unit)) if matches_ignoring_case(unit, n) => {
            return Some((value, 1));
        },
        _ => {},
    }
    if keyword(first, n) {
        Some((1, 1))
    } else if keyword(first, dash_n) {
        Some((-1, 1))
    } else if items.len() >= 2 && delim_item(first, 0x2B) && plus_adjacent && keyword(
        at(items, 1),
        n,
    ) {
        Some((1, 2))
    } else {
        None
    }
}

/// [`single_clause`].
fn single_clause_of(items: &[&ExecItem], plus_adjacent: bool) -> Option<(i32, i32)> {
    if items.is_empty() {
        return None;
    }
    let last = at(items, items.len().saturating_sub(1));
    let plussed = items.len() == 2 && delim_item(at(items, 0), 0x2B) && plus_adjacent;
    match integer_dimension(last) {
        Some((value, unit)) if items.len() == 1 && n_dash_digits(unit, 0) => {
            return Some((value, remainder(unit, 1)));
        },
        _ => {},
    }
    if let Some(ExecToken::Ident { value }) = token_of(last) {
        if (items.len() == 1 || plussed) && n_dash_digits(value, 0) {
            return Some((1, remainder(value, 1)));
        }
        if items.len() == 1 && !value.is_empty() && *item(value, 0) == 0x2D && n_dash_digits(
            value,
            1,
        ) {
            return Some((-1, remainder(value, 2)));
        }
    }
    None
}

/// [`a_n_plus_b`] on the rows `lo` up to `hi`, with A and B clamped.
fn a_n_plus_b_of(src: &ExecParsed, lo: usize, hi: usize) -> Option<(i32, i32)>
    requires
        src_ok(*src),
{
    let value = read_items(src, lo, hi);
    let value = value.as_slice();
    let start = skip_ws(value, 0, value.len());
    let plus_adjacent = start.saturating_add(1) < value.len() && !matches!(
        tok(value, start.saturating_add(1), value.len()),
        Some(ExecToken::Whitespace)
    );
    let mut items: Vec<&ExecItem> = Vec::new();
    let mut k = 0;
    while k < value.len()
        decreases value.len() - k,
    {
        let it = item(value, k);
        if !matches!(token_of(it), Some(ExecToken::Whitespace)) {
            items.push(it);
        }
        k = k.saturating_add(1);
    }
    let items = items.as_slice();
    let count = items.len();
    if count == 0 {
        return None;
    }
    if count == 1 && keyword(at(items, 0), &[0x6F, 0x64, 0x64]) {
        return Some((2, 1));
    }
    if count == 1 && keyword(at(items, 0), &[0x65, 0x76, 0x65, 0x6E]) {
        return Some((2, 0));
    }
    match integer_of(at(items, 0)) {
        Some(number) if count == 1 => {
            return Some((0, clamped_value(number)));
        },
        _ => {},
    }
    let last = at(items, count.saturating_sub(1));
    match a_of(items, plus_adjacent, false) {
        Some((a, taken)) => {
            if count == taken {
                Some((a, 0))
            } else if count == taken.saturating_add(1) {
                signed_of(last).map(|b| (a, b))
            } else if count == taken.saturating_add(2) {
                let b = signless_of(last)?;
                let sign = at(items, taken);
                if delim_item(sign, 0x2B) {
                    Some((a, b))
                } else if delim_item(sign, 0x2D) {
                    Some((a, negate(b)))
                } else {
                    None
                }
            } else {
                None
            }
        },
        None => match a_of(items, plus_adjacent, true) {
            Some((a, taken)) if count == taken.saturating_add(1) => signless_of(last).map(
                |b| (a, negate(b)),
            ),
            _ => single_clause_of(items, plus_adjacent),
        },
    }
}

// ------------------------------------------------------------------------------------
// The productions with selectors inside
// ------------------------------------------------------------------------------------

/// The arrays being built, and whether functions nested more deeply than the parser
/// follows: then the whole parse fails, even where the nesting was inside a forgiving list.
pub struct Build {
    /// The arrays.
    pub selectors: ExecSelectors,
    /// True once the nesting limit was met.
    pub too_deep: bool,
}

/// Appends a list of complex selectors to the arrays, and returns its index.
fn push_list(out: &mut Build, complexes: Vec<ExecComplex>) -> usize {
    let lo = out.selectors.complexes.len();
    let mut complexes = complexes;
    out.selectors.complexes.append(&mut complexes);
    let hi = out.selectors.complexes.len();
    out.selectors.lists.push(ExecRange { lo, hi });
    out.selectors.lists.len().saturating_sub(1)
}

/// [`functional_pseudo_class`]: `name(` the rows `lo` up to `hi` `)`.
fn functional_pseudo_class_of(
    src: &ExecParsed,
    name: &[u32],
    lo: usize,
    hi: usize,
    out: &mut Build,
    depth: usize,
) -> Option<ExecSimple>
    requires
        src_ok(*src),
    decreases depth, 0int,
{
    if depth == 0 {
        out.too_deep = true;
        return None;
    }
    let inner = depth.saturating_sub(1);
    if matches_ignoring_case(name, &[0x69, 0x73]) {
        let value = read_items(src, lo, hi);
        let list = forgiving_list_of(src, value.as_slice(), out, inner);
        Some(ExecSimple::Is { list })
    } else if matches_ignoring_case(name, &[0x77, 0x68, 0x65, 0x72, 0x65]) {
        let value = read_items(src, lo, hi);
        let list = forgiving_list_of(src, value.as_slice(), out, inner);
        Some(ExecSimple::Where { list })
    } else if matches_ignoring_case(name, &[0x6E, 0x6F, 0x74]) {
        let value = read_items(src, lo, hi);
        let value = value.as_slice();
        let list = complex_list_of(src, value, 0, value.len(), true, out, inner)?;
        Some(ExecSimple::Not { list })
    } else {
        let kind = nth_of(name)?;
        let (a, b) = a_n_plus_b_of(src, lo, hi)?;
        Some(ExecSimple::Nth { kind, a, b })
    }
}

/// [`subclass_selector`].
fn subclass_selector_at(
    src: &ExecParsed,
    items: &[ExecItem],
    i: usize,
    hi: usize,
    out: &mut Build,
    depth: usize,
) -> Found<ExecSimple>
    requires
        src_ok(*src),
    decreases depth, 1int,
{
    if i >= hi || i >= items.len() {
        return Found::Absent;
    }
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    match item(items, i) {
        ExecItem::Token { token: ExecToken::Hash { value, is_id } } => if *is_id {
            Found::Here(ExecSimple::Id { name: copy(value) }, i1)
        } else {
            Found::Invalid
        },
        ExecItem::Token { token: ExecToken::Delim { value: 0x2E } } => match ident(items, i1, hi) {
            Some(name) => Found::Here(ExecSimple::Class { name: copy(name) }, i2),
            None => Found::Invalid,
        },
        ExecItem::Block { token: ExecToken::OpenSquare, lo, hi: end } => match attribute_selector_of(
            src,
            *lo,
            *end,
        ) {
            Some(simple) => Found::Here(simple, i1),
            None => Found::Invalid,
        },
        ExecItem::Token { token: ExecToken::Colon } => {
            if is_colon(items, i1, hi) {
                return Found::Absent;
            }
            if i1 >= hi || i1 >= items.len() {
                return Found::Invalid;
            }
            match item(items, i1) {
                ExecItem::Token { token: ExecToken::Ident { value } } => {
                    if pseudo_element_of(value).is_some() {
                        Found::Absent
                    } else {
                        match pseudo_class_of(value) {
                            Some(class) => Found::Here(ExecSimple::PseudoClass { class }, i2),
                            None => Found::Invalid,
                        }
                    }
                },
                ExecItem::Function { name, lo, hi: end } => match functional_pseudo_class_of(
                    src,
                    name,
                    *lo,
                    *end,
                    out,
                    depth,
                ) {
                    Some(simple) => Found::Here(simple, i2),
                    None => Found::Invalid,
                },
                _ => Found::Invalid,
            }
        },
        _ => Found::Absent,
    }
}

/// [`compound_selector`], with [`subclass_selectors`] as its loop.
fn compound_selector_at(
    src: &ExecParsed,
    items: &[ExecItem],
    i: usize,
    hi: usize,
    no_pseudo: bool,
    out: &mut Build,
    depth: usize,
) -> Option<(Vec<ExecSimple>, usize)>
    requires
        src_ok(*src),
    decreases depth, 2int,
{
    let mut acc: Vec<ExecSimple> = Vec::new();
    if i > hi {
        return Some((acc, i));
    }
    let mut j = match type_selector_at(items, i, hi) {
        Found::Invalid => {
            return None;
        },
        Found::Absent => i,
        Found::Here(value, next) => {
            if !(i < next && next <= hi) {
                return None;
            }
            acc.push(value);
            next
        },
    };
    loop
        invariant
            j <= hi,
            src_ok(*src),
        decreases hi - j,
    {
        match subclass_selector_at(src, items, j, hi, out, depth) {
            Found::Invalid => {
                return None;
            },
            Found::Here(value, next) => {
                if !(j < next && next <= hi) {
                    return None;
                }
                acc.push(value);
                j = next;
            },
            Found::Absent => {
                let end = pseudo_compound_at(items, j, hi, &mut acc, no_pseudo)?;
                return Some((acc, end));
            },
        }
    }
}

/// [`complex_selector`] on `lo` up to `hi`, with [`complex_selector_loop`] as its loop: the
/// complex selector, its compounds and combinators appended to the arrays.
fn complex_selector_of(
    src: &ExecParsed,
    items: &[ExecItem],
    lo: usize,
    hi: usize,
    no_pseudo: bool,
    out: &mut Build,
    depth: usize,
) -> Option<ExecComplex>
    requires
        src_ok(*src),
    decreases depth, 3int,
{
    let start = skip_ws(items, lo, hi);
    if start >= hi || start < lo {
        return None;
    }
    let mut compounds: Vec<ExecRange> = Vec::new();
    let mut combinators: Vec<Combinator> = Vec::new();
    let mut i = start;
    loop
        invariant
            i < hi,
            src_ok(*src),
        decreases hi - i,
    {
        let (compound, next) = compound_selector_at(src, items, i, hi, no_pseudo, out, depth)?;
        if next <= i || next > hi {
            return None;
        }
        let pseudo = holds_pseudo_element(compound.as_slice());
        let first = out.selectors.simples.len();
        let mut compound = compound;
        out.selectors.simples.append(&mut compound);
        compounds.push(ExecRange { lo: first, hi: out.selectors.simples.len() });
        let after = skip_ws(items, next, hi);
        if after >= hi {
            break;
        }
        if pseudo {
            return None;
        }
        match combinator_of(items, after, hi) {
            Some(combinator) => {
                let begin = skip_ws(items, after.saturating_add(1), hi);
                if begin >= hi || begin <= i {
                    return None;
                }
                combinators.push(combinator);
                i = begin;
            },
            None => {
                if after > next {
                    combinators.push(Combinator::Descendant);
                    i = after;
                } else {
                    return None;
                }
            },
        }
    }
    let c_lo = out.selectors.compounds.len();
    out.selectors.compounds.append(&mut compounds);
    let k_lo = out.selectors.combinators.len();
    out.selectors.combinators.append(&mut combinators);
    Some(
        ExecComplex {
            compounds: ExecRange { lo: c_lo, hi: out.selectors.compounds.len() },
            combinators: ExecRange { lo: k_lo, hi: out.selectors.combinators.len() },
        },
    )
}

/// [`complex_list`] on `lo` up to `hi`: the index of the list, appended to the arrays.
fn complex_list_of(
    src: &ExecParsed,
    items: &[ExecItem],
    lo: usize,
    hi: usize,
    no_pseudo: bool,
    out: &mut Build,
    depth: usize,
) -> Option<usize>
    requires
        src_ok(*src),
    decreases depth, 4int,
{
    let mut complexes: Vec<ExecComplex> = Vec::new();
    if lo > hi {
        return None;
    }
    let mut i = lo;
    loop
        invariant
            i <= hi,
            src_ok(*src),
        decreases hi - i,
    {
        let comma = next_comma_at(items, i, hi);
        if comma < i || comma > hi {
            return None;
        }
        let selector = complex_selector_of(src, items, i, comma, no_pseudo, out, depth)?;
        complexes.push(selector);
        if comma >= hi {
            break;
        }
        i = comma.saturating_add(1);
    }
    Some(push_list(out, complexes))
}

/// [`parse_as_a_forgiving_selector_list`] on all of `items`: the index of the list.
fn forgiving_list_of(src: &ExecParsed, items: &[ExecItem], out: &mut Build, depth: usize) -> usize
    requires
        src_ok(*src),
    decreases depth, 4int,
{
    let hi = items.len();
    let mut complexes: Vec<ExecComplex> = Vec::new();
    if skip_ws(items, 0, hi) < hi {
        let mut i: usize = 0;
        while i < hi
            invariant
                src_ok(*src),
            decreases hi - i,
        {
            let comma = next_comma_at(items, i, hi);
            if comma < i || comma > hi {
                break;
            }
            if let Some(selector) = complex_selector_of(src, items, i, comma, true, out, depth) {
                complexes.push(selector);
            }
            if comma >= hi {
                break;
            }
            i = comma.saturating_add(1);
        }
    }
    push_list(out, complexes)
}

/// §21.1 "parse a selector" from `input`: the selectors, whose result is the last list, or
/// `None` for failure, or if functions nest more deeply than
/// [`super::contract::MAX_NESTING`]. What is returned has passed [`super::exec_check`].
pub fn parse_selector(input: &[u32]) -> (r: Option<ExecSelectors>)
    requires
        clazel_css::parser::contract::parser_input_requires(input@),
    ensures
        match r {
            Some(s) => super::exec_check::checked(s),
            None => true,
        },
{
    let parsed = clazel_css::parser::exec_parse::parse_component_values(input);
    let items = read_items(&parsed, 0, parsed.output.rows.len());
    let mut out = Build {
        selectors: ExecSelectors {
            simples: Vec::new(),
            compounds: Vec::new(),
            combinators: Vec::new(),
            complexes: Vec::new(),
            lists: Vec::new(),
        },
        too_deep: false,
    };
    let items = items.as_slice();
    complex_list_of(&parsed, items, 0, items.len(), false, &mut out, super::contract::MAX_NESTING)?;
    if !out.too_deep && super::exec_check::check(&out.selectors) {
        Some(out.selectors)
    } else {
        None
    }
}

} // verus!
