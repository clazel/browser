//! §21.1 "parse a selector": the executable parser.
//!
//! Each function is the spec function of the same name in [`super::spec`], step for step, over
//! the [`ExecItem`]s of a list, and ensures its relation to it: [`parse_selector`] ensures
//! [`super::contract::parse_selector_ensures`], and the functions below it ensure what it
//! needs of them. A production that builds selectors appends to the arrays of a [`Build`] and
//! leaves what was built before as it was (`exec_grow`); a selector not yet in a list is
//! viewed in the arrays as they are (`pv_seq`, `pv_compounds`, `pv_complex`), and a loop's
//! invariant says that the spec's loop from the start equals the spec's loop from the
//! position it is at, with what has been read so far. Nesting past
//! [`super::contract::MAX_NESTING`] sets [`Build::too_deep`], and each relation holds unless
//! it is set, which only a list nested more deeply than the limit can do.
//!
//! The one thing taken on trust is that a `Vec` of the arrays never holds `usize::MAX`
//! elements (`axioms.rs`).

#[cfg(verus_only)]
use super::axioms::axiom_lengths;
use super::contract::*;
use super::exec_anb::a_n_plus_b_of;
#[cfg(verus_only)]
use super::exec_grow::*;
use super::exec_items::*;
#[cfg(verus_only)]
use super::exec_steps::*;
#[cfg(verus_only)]
use super::lemmas::theorem_parse_total;
use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_css::parser::exec_declaration::matches_ignoring_case;
use clazel_css::parser::exec_parse::ExecParsed;
#[cfg(verus_only)]
use clazel_css::tokenizer::exec::view_token;
use clazel_css::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Reading items
// ------------------------------------------------------------------------------------

/// The token at `i`, if it is one, below `hi`.
pub(crate) fn tok<'a>(src: &ExecParsed, items: &'a [ExecItem], i: usize, hi: usize) -> (r: Option<&'a ExecToken>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Some(t) => token_at(view_items(*src, items@), i as int, hi as int) == Some(view_token(*t)),
            None => token_at(view_items(*src, items@), i as int, hi as int) is None,
        },
{
    let _ = src;
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
fn is_delim(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize, c: u32) -> (r: bool)
    requires
        hi <= items.len(),
    ensures
        r == is_delim_at(view_items(*src, items@), i as int, hi as int, c),
{
    matches!(tok(src, items, i, hi), Some(ExecToken::Delim { value }) if *value == c)
}

/// The token at `i` is `:`.
fn is_colon(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: bool)
    requires
        hi <= items.len(),
    ensures
        r == is_token_at(view_items(*src, items@), i as int, hi as int, Token::Colon),
{
    matches!(tok(src, items, i, hi), Some(ExecToken::Colon))
}

/// [`ident_at`].
fn ident<'a>(src: &ExecParsed, items: &'a [ExecItem], i: usize, hi: usize) -> (r: Option<&'a Vec<u32>>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Some(v) => ident_at(view_items(*src, items@), i as int, hi as int) == Some(v@),
            None => ident_at(view_items(*src, items@), i as int, hi as int) is None,
        },
{
    match tok(src, items, i, hi) {
        Some(ExecToken::Ident { value }) => Some(value),
        _ => None,
    }
}

/// [`skip_whitespace`].
pub(crate) fn skip_ws(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: usize)
    requires
        hi <= items.len(),
    ensures
        r == skip_whitespace(view_items(*src, items@), i as int, hi as int),
        i <= hi ==> i <= r <= hi,
        i > hi ==> r == i,
{
    let ghost l = view_items(*src, items@);
    let mut j = i;
    while j < hi && matches!(tok(src, items, j, hi), Some(ExecToken::Whitespace))
        invariant
            hi <= items.len(),
            l == view_items(*src, items@),
            i <= j,
            i <= hi ==> j <= hi,
            i > hi ==> j == i,
            skip_whitespace(l, i as int, hi as int) == skip_whitespace(l, j as int, hi as int),
        decreases hi - j,
    {
        proof {
            assert(is_whitespace_token(l[j as int]));
            assert(whitespace_run(l, j as int, hi as int) == 1 + whitespace_run(l, j as int + 1, hi as int));
        }
        j = j.saturating_add(1);
    }
    proof {
        if j < hi {
            assert(!is_whitespace_token(l[j as int]));
        }
        assert(whitespace_run(l, j as int, hi as int) == 0);
    }
    j
}

/// [`next_comma`].
fn next_comma_at(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: usize)
    requires
        hi <= items.len(),
    ensures
        r == next_comma(view_items(*src, items@), i as int, hi as int),
        i <= hi ==> i <= r <= hi,
        i > hi ==> r == i,
{
    let ghost l = view_items(*src, items@);
    let mut j = i;
    while j < hi && !matches!(tok(src, items, j, hi), Some(ExecToken::Comma))
        invariant
            hi <= items.len(),
            l == view_items(*src, items@),
            i <= j,
            i <= hi ==> j <= hi,
            i > hi ==> j == i,
            next_comma(l, i as int, hi as int) == next_comma(l, j as int, hi as int),
        decreases hi - j,
    {
        proof {
            assert(is(l[j as int], Token::Comma) == false);
        }
        j = j.saturating_add(1);
    }
    proof {
        if j < hi {
            assert(is(l[j as int], Token::Comma));
        }
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
fn pseudo_class_of(name: &[u32]) -> (r: Option<PseudoClass>)
    ensures
        r == pseudo_class_named(name@),
{
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
fn pseudo_element_of(name: &[u32]) -> (r: Option<PseudoElement>)
    ensures
        r == pseudo_element_named(name@),
{
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
fn nth_of(name: &[u32]) -> (r: Option<NthKind>)
    ensures
        r == nth_named(name@),
{
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
fn user_action_class(class: PseudoClass) -> (r: bool)
    ensures
        r == is_user_action(class),
{
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
fn type_selector_at(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: Found<ExecSimple>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Found::Absent => type_selector(view_items(*src, items@), i as int, hi as int) is Absent,
            Found::Invalid => type_selector(view_items(*src, items@), i as int, hi as int) is Invalid,
            Found::Here(e, n) => plain(e) && type_selector(view_items(*src, items@), i as int, hi as int)
                == (Step::Found { value: view_plain(e), next: n as int }),
        },
{
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if let Some(name) = ident(src, items, i, hi) {
        if is_delim(src, items, i1, hi, 0x7C) {
            Found::Invalid
        } else {
            Found::Here(ExecSimple::Type { ns: NsPrefix::Absent, name: copy(name) }, i1)
        }
    } else if is_delim(src, items, i, hi, 0x2A) {
        if is_delim(src, items, i1, hi, 0x7C) {
            if let Some(name) = ident(src, items, i2, hi) {
                Found::Here(ExecSimple::Type { ns: NsPrefix::Any, name: copy(name) }, i3)
            } else if is_delim(src, items, i2, hi, 0x2A) {
                Found::Here(ExecSimple::Universal { ns: NsPrefix::Any }, i3)
            } else {
                Found::Invalid
            }
        } else {
            Found::Here(ExecSimple::Universal { ns: NsPrefix::Absent }, i1)
        }
    } else if is_delim(src, items, i, hi, 0x7C) {
        if let Some(name) = ident(src, items, i1, hi) {
            Found::Here(ExecSimple::Type { ns: NsPrefix::NoNamespace, name: copy(name) }, i2)
        } else if is_delim(src, items, i1, hi, 0x2A) {
            Found::Here(ExecSimple::Universal { ns: NsPrefix::NoNamespace }, i2)
        } else {
            Found::Invalid
        }
    } else {
        Found::Absent
    }
}

/// [`attribute_name`].
fn attribute_name_at(src: &ExecParsed, v: &[ExecItem], i: usize) -> (r: Option<(NsPrefix, Vec<u32>, usize)>)
    ensures
        match r {
            Some((ns, name, n)) => attribute_name(view_items(*src, v@), i as int) == Some(
                (ns, name@, n as int),
            ),
            None => attribute_name(view_items(*src, v@), i as int) is None,
        },
{
    let hi = v.len();
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if let Some(name) = ident(src, v, i, hi) {
        if is_delim(src, v, i1, hi, 0x7C) && ident(src, v, i2, hi).is_some() {
            None
        } else {
            Some((NsPrefix::Absent, copy(name), i1))
        }
    } else if is_delim(src, v, i, hi, 0x2A) && is_delim(src, v, i1, hi, 0x7C) {
        match ident(src, v, i2, hi) {
            Some(name) => Some((NsPrefix::Any, copy(name), i3)),
            None => None,
        }
    } else if is_delim(src, v, i, hi, 0x7C) {
        match ident(src, v, i1, hi) {
            Some(name) => Some((NsPrefix::NoNamespace, copy(name), i2)),
            None => None,
        }
    } else {
        None
    }
}

/// [`attr_matcher`].
fn attr_matcher_at(src: &ExecParsed, v: &[ExecItem], i: usize) -> (r: Option<(AttrMatcher, usize)>)
    ensures
        match r {
            Some((m, n)) => attr_matcher(view_items(*src, v@), i as int) == Some((m, n as int)),
            None => attr_matcher(view_items(*src, v@), i as int) is None,
        },
{
    let hi = v.len();
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    if is_delim(src, v, i, hi, 0x3D) {
        Some((AttrMatcher::Equals, i1))
    } else if is_delim(src, v, i1, hi, 0x3D) {
        if is_delim(src, v, i, hi, 0x7E) {
            Some((AttrMatcher::Includes, i2))
        } else if is_delim(src, v, i, hi, 0x7C) {
            Some((AttrMatcher::DashMatch, i2))
        } else if is_delim(src, v, i, hi, 0x5E) {
            Some((AttrMatcher::Prefix, i2))
        } else if is_delim(src, v, i, hi, 0x24) {
            Some((AttrMatcher::Suffix, i2))
        } else if is_delim(src, v, i, hi, 0x2A) {
            Some((AttrMatcher::Substring, i2))
        } else {
            None
        }
    } else {
        None
    }
}

/// [`attribute_selector`], on the rows `lo` up to `hi` of the `[]` block's value.
fn attribute_selector_of(src: &ExecParsed, lo: usize, hi: usize) -> (r: Option<ExecSimple>)
    requires
        src_ok(*src),
    ensures
        match r {
            Some(e) => plain(e) && attribute_selector(rows_list(*src, lo as int, hi as int)) == Some(
                view_plain(e),
            ),
            None => attribute_selector(rows_list(*src, lo as int, hi as int)) is None,
        },
{
    let v = read_items(src, lo, hi);
    let v = v.as_slice();
    let end = v.len();
    let ghost l = view_items(*src, v@);
    proof {
        assert(l == rows_list(*src, lo as int, hi as int));
        assert(l.len() == end);
    }
    let first = skip_ws(src, v, 0, end);
    let (ns, name, after_name) = match attribute_name_at(src, v, first) {
        Some(t) => t,
        None => {
            proof {
                assert(attribute_selector(l) is None);
            }
            return None;
        },
    };
    let at_matcher = skip_ws(src, v, after_name, end);
    if at_matcher >= end {
        let r = ExecSimple::Attribute { ns, name, test: None };
        proof {
            assert(attribute_selector(l) == Some(view_plain(r)));
        }
        return Some(r);
    }
    let (matcher, after_matcher) = match attr_matcher_at(src, v, at_matcher) {
        Some(t) => t,
        None => {
            proof {
                assert(attribute_selector(l) is None);
            }
            return None;
        },
    };
    let at_value = skip_ws(src, v, after_matcher, end);
    let value = match tok(src, v, at_value, end) {
        Some(ExecToken::String { value }) => copy(value),
        Some(ExecToken::Ident { value }) => copy(value),
        _ => {
            proof {
                assert(attribute_selector(l) is None);
            }
            return None;
        },
    };
    proof {
        assert(at_value < end);
    }
    let at_modifier = skip_ws(src, v, at_value.saturating_add(1), end);
    if at_modifier >= end {
        let r = ExecSimple::Attribute { ns, name, test: Some(ExecAttrTest { matcher, value, flag: None }) };
        proof {
            assert(attribute_selector(l) == Some(view_plain(r)));
        }
        return Some(r);
    }
    let flag = match ident(src, v, at_modifier, end) {
        Some(m) => {
            let m = m.as_slice();
            let is_i = matches_ignoring_case(m, &[0x69]);
            let is_s = matches_ignoring_case(m, &[0x73]);
            proof {
                assert(seq![0x69u32] == (&[0x69u32])@);
                assert(seq![0x73u32] == (&[0x73u32])@);
            }
            if is_i {
                Some(CaseFlag::I)
            } else if is_s {
                Some(CaseFlag::S)
            } else {
                None
            }
        },
        None => None,
    };
    proof {
        assert(at_modifier < end);
        let spec_flag = match ident_at(l, at_modifier as int, end as int) {
            Some(m) => if ascii_case_insensitive_match(m, seq![0x69u32]) {
                Some(CaseFlag::I)
            } else if ascii_case_insensitive_match(m, seq![0x73u32]) {
                Some(CaseFlag::S)
            } else {
                None
            },
            None => None,
        };
        assert(flag == spec_flag);
    }
    let after_flag = skip_ws(src, v, at_modifier.saturating_add(1), end);
    if flag.is_some() && after_flag >= end {
        let r = ExecSimple::Attribute { ns, name, test: Some(ExecAttrTest { matcher, value, flag }) };
        proof {
            assert(attribute_selector(l) == Some(view_plain(r)));
        }
        Some(r)
    } else {
        proof {
            assert(attribute_selector(l) is None);
        }
        None
    }
}

/// [`pseudo_element`].
fn pseudo_element_at(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: Found<PseudoElement>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Found::Absent => pseudo_element(view_items(*src, items@), i as int, hi as int) is Absent,
            Found::Invalid => pseudo_element(view_items(*src, items@), i as int, hi as int) is Invalid,
            Found::Here(e, n) => pseudo_element(view_items(*src, items@), i as int, hi as int)
                == (Step::Found { value: e, next: n as int }),
        },
{
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let i3 = i.saturating_add(3);
    if !is_colon(src, items, i, hi) {
        return Found::Absent;
    }
    if is_colon(src, items, i1, hi) {
        match ident(src, items, i2, hi) {
            Some(name) => match pseudo_element_of(name) {
                Some(element) => Found::Here(element, i3),
                None => Found::Invalid,
            },
            None => Found::Invalid,
        }
    } else {
        match ident(src, items, i1, hi) {
            Some(name) => match pseudo_element_of(name) {
                Some(element) => Found::Here(element, i2),
                None => Found::Absent,
            },
            None => Found::Absent,
        }
    }
}

/// [`user_actions`]: the user action pseudo-classes after a pseudo-element, onto `acc`.
fn user_actions_at(
    src: &ExecParsed,
    items: &[ExecItem],
    i: usize,
    hi: usize,
    acc: &mut Vec<ExecSimple>,
    s: Ghost<ExecSelectors>,
) -> (r: Option<usize>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Some(n) => user_actions(view_items(*src, items@), i as int, hi as int, pv_seq(s@, old(acc)@))
                == Some((pv_seq(s@, final(acc)@), n as int)),
            None => user_actions(view_items(*src, items@), i as int, hi as int, pv_seq(s@, old(acc)@)) is None,
        },
        acc_in(s@, old(acc)@) ==> acc_in(s@, final(acc)@),
{
    let _ = s;
    let ghost l = view_items(*src, items@);
    let ghost acc0 = old(acc)@;
    let ghost start = pv_seq(s@, acc0);
    let mut j = i;
    while j < hi
        invariant
            hi <= items.len(),
            l == view_items(*src, items@),
            i <= j,
            j <= hi || j == i,
            user_actions(l, i as int, hi as int, start) == user_actions(l, j as int, hi as int, pv_seq(s@, acc@)),
            acc0 == old(acc)@,
            start == pv_seq(s@, acc0),
            acc_in(s@, acc0) ==> acc_in(s@, acc@),
        decreases hi - j,
    {
        if !is_colon(src, items, j, hi) {
            proof {
                assert(user_action(l, j as int, hi as int) is Absent);
                assert(user_actions(l, j as int, hi as int, pv_seq(s@, acc@)) == Some((pv_seq(s@, acc@), j as int)));
                assert(user_actions(l, i as int, hi as int, start) == Some((pv_seq(s@, acc@), j as int)));
            }
            return Some(j);
        }
        let name = match ident(src, items, j.saturating_add(1), hi) {
            Some(n) => n,
            None => {
                proof {
                    assert(user_action(l, j as int, hi as int) is Invalid);
                }
                return None;
            },
        };
        let class = match pseudo_class_of(name) {
            Some(c) => c,
            None => {
                proof {
                    assert(user_action(l, j as int, hi as int) is Invalid);
                }
                return None;
            },
        };
        if !user_action_class(class) {
            proof {
                assert(user_action(l, j as int, hi as int) is Invalid);
            }
            return None;
        }
        proof {
            lemma_pv_push(s@, acc@, ExecSimple::PseudoClass { class });
            assert(j + 1 < hi);
            assert(user_action(l, j as int, hi as int) == (Step::Found { value: class, next: j as int + 2 }));
            let a0 = pv_seq(s@, acc@);
            assert(user_actions(l, j as int, hi as int, a0) == user_actions(
                l,
                j as int + 2,
                hi as int,
                a0.push(Simple::PseudoClass { class }),
            ));
        }
        acc.push(ExecSimple::PseudoClass { class });
        j = j.saturating_add(2);
    }
    proof {
        assert(user_action(l, j as int, hi as int) is Absent);
        assert(user_actions(l, j as int, hi as int, pv_seq(s@, acc@)) == Some((pv_seq(s@, acc@), j as int)));
    }
    Some(j)
}

/// [`pseudo_compound`].
fn pseudo_compound_at(
    src: &ExecParsed,
    items: &[ExecItem],
    i: usize,
    hi: usize,
    acc: &mut Vec<ExecSimple>,
    no_pseudo: bool,
    s: Ghost<ExecSelectors>,
) -> (r: Option<usize>)
    requires
        hi <= items.len(),
    ensures
        match r {
            Some(n) => pseudo_compound(
                view_items(*src, items@),
                i as int,
                hi as int,
                pv_seq(s@, old(acc)@),
                no_pseudo,
            ) == Some((pv_seq(s@, final(acc)@), n as int)),
            None => pseudo_compound(
                view_items(*src, items@),
                i as int,
                hi as int,
                pv_seq(s@, old(acc)@),
                no_pseudo,
            ) is None,
        },
        acc_in(s@, old(acc)@) ==> acc_in(s@, final(acc)@),
{
    match pseudo_element_at(src, items, i, hi) {
        Found::Absent => Some(i),
        Found::Invalid => None,
        Found::Here(element, next) => {
            if no_pseudo {
                return None;
            }
            proof {
                lemma_pv_push(s@, acc@, ExecSimple::PseudoElement { element });
            }
            acc.push(ExecSimple::PseudoElement { element });
            user_actions_at(src, items, next, hi, acc, s)
        },
    }
}

/// [`has_pseudo_element`].
fn holds_pseudo_element(compound: &[ExecSimple], s: Ghost<ExecSelectors>) -> (r: bool)
    ensures
        r == has_pseudo_element(pv_seq(s@, compound@)),
{
    let _ = s;
    let mut k = 0;
    while k < compound.len()
        invariant
            k <= compound.len(),
            forall|m: int| 0 <= m < k ==> !(#[trigger] compound@[m] is PseudoElement),
        decreases compound.len() - k,
    {
        if matches!(item(compound, k), ExecSimple::PseudoElement { .. }) {
            proof {
                lemma_pseudo_element_within(s@, compound@, k as int);
            }
            return true;
        }
        k = k.saturating_add(1);
    }
    proof {
        lemma_no_pseudo_element(s@, compound@);
    }
    false
}

/// [`combinator_at`].
fn combinator_of(src: &ExecParsed, items: &[ExecItem], i: usize, hi: usize) -> (r: Option<Combinator>)
    requires
        hi <= items.len(),
    ensures
        r == combinator_at(view_items(*src, items@), i as int, hi as int),
{
    if is_delim(src, items, i, hi, 0x3E) {
        Some(Combinator::Child)
    } else if is_delim(src, items, i, hi, 0x2B) {
        Some(Combinator::NextSibling)
    } else if is_delim(src, items, i, hi, 0x7E) {
        Some(Combinator::SubsequentSibling)
    } else {
        None
    }
}

// ------------------------------------------------------------------------------------
// Lemmas about the views
// ------------------------------------------------------------------------------------

/// A pseudo-element among the simple selectors is one of their views.
proof fn lemma_pseudo_element_within(s: ExecSelectors, acc: Seq<ExecSimple>, k: int)
    requires
        0 <= k < acc.len(),
        acc[k] is PseudoElement,
    ensures
        has_pseudo_element(pv_seq(s, acc)),
{
    let v = pv_seq(s, acc);
    lemma_pv_index(s, acc, k);
    assert(v[k] is PseudoElement);
    lemma_within_from(v, k, v.len() as int);
}

/// If a pseudo-element is among the first `n`, `pseudo_element_within` the first `n`.
proof fn lemma_within_from(v: Seq<Simple>, k: int, n: int)
    requires
        0 <= k < n <= v.len(),
        v[k] is PseudoElement,
    ensures
        pseudo_element_within(v, n),
    decreases n,
{
    if k < n - 1 {
        lemma_within_from(v, k, n - 1);
    }
}

/// With none of the simple selectors a pseudo-element, the compound has none.
proof fn lemma_no_pseudo_element(s: ExecSelectors, acc: Seq<ExecSimple>)
    requires
        forall|m: int| 0 <= m < acc.len() ==> !(#[trigger] acc[m] is PseudoElement),
    ensures
        !has_pseudo_element(pv_seq(s, acc)),
{
    let v = pv_seq(s, acc);
    lemma_pv_len(s, acc);
    lemma_none_within(v, acc, s, v.len() as int);
}

/// None of the first `n` is a pseudo-element.
proof fn lemma_none_within(v: Seq<Simple>, acc: Seq<ExecSimple>, s: ExecSelectors, n: int)
    requires
        v == pv_seq(s, acc),
        0 <= n <= v.len(),
        forall|m: int| 0 <= m < acc.len() ==> !(#[trigger] acc[m] is PseudoElement),
    ensures
        !pseudo_element_within(v, n),
    decreases n,
{
    lemma_pv_len(s, acc);
    if n > 0 {
        lemma_none_within(v, acc, s, n - 1);
        assert(!(acc[n - 1] is PseudoElement));
        lemma_pv_index(s, acc, n - 1);
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

/// What every step leaves: the arrays are well-formed, only grown, and once the nesting
/// limit is met it stays met.
pub open spec fn step_ok(before: Build, after: Build) -> bool {
    &&& ranges_wf(after.selectors)
    &&& refs_lt(after.selectors)
    &&& grows(before.selectors, after.selectors)
    &&& before.too_deep ==> after.too_deep
}

/// The component values in `l` nest no more deeply than `d`.
pub open spec fn depth_ok(l: Seq<ComponentValue>, d: int) -> bool {
    values_depth(l, l.len()) <= d
}

/// Each of the first `n` values is within the depth of the first `n`.
proof fn lemma_values_depth_ge(l: Seq<ComponentValue>, n: nat, k: int)
    requires
        0 <= k < n <= l.len(),
    ensures
        value_depth(l[k]) <= values_depth(l, n),
    decreases n,
{
    if k < n - 1 {
        lemma_values_depth_ge(l, (n - 1) as nat, k);
    }
}

/// A function in a list that nests within `d` holds a list that nests within `d - 1`.
proof fn lemma_fn_depth(l: Seq<ComponentValue>, d: int, k: int)
    requires
        depth_ok(l, d),
        0 <= k < l.len(),
        l[k] is Function,
    ensures
        d >= 1,
        depth_ok(l[k]->Function_value, d - 1),
{
    lemma_values_depth_ge(l, l.len(), k);
}

/// Appends a list of complex selectors to the arrays, and returns its index.
fn push_list(out: &mut Build, complexes: Vec<ExecComplex>) -> (r: usize)
    requires
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
        cs_in(old(out).selectors, complexes@),
    ensures
        step_ok(*old(out), *final(out)),
        final(out).too_deep == old(out).too_deep,
        r == old(out).selectors.lists.len(),
        final(out).selectors.lists.len() == old(out).selectors.lists.len() + 1,
        view_list(final(out).selectors, r as int) == pv_complexes(old(out).selectors, complexes@),
{
    let ghost s0 = out.selectors;
    let ghost cs = complexes@;
    let lo = out.selectors.complexes.len();
    let mut complexes = complexes;
    out.selectors.complexes.append(&mut complexes);
    let hi = out.selectors.complexes.len();
    out.selectors.lists.push(ExecRange { lo, hi });
    let r = out.selectors.lists.len().saturating_sub(1);
    proof {
        let s1 = out.selectors;
        let ghost g = s1;
        axiom_lengths(&g);
        assert(r == s0.lists.len());
        assert(s1.lists.len() == s0.lists.len() + 1);
        assert(hi == lo + cs.len());
        assert(grows(s0, s1)) by {
            assert forall|i: int| 0 <= i < s0.complexes.len() implies s1.complexes[i] == s0.complexes[i] by {}
            assert forall|i: int| 0 <= i < s0.lists.len() implies s1.lists[i] == s0.lists[i] by {}
        }
        assert(ranges_wf(s1)) by {
            assert forall|i: int| 0 <= i < s1.complexes.len() implies {
                &&& #[trigger] s1.complexes[i].compounds.lo <= s1.complexes[i].compounds.hi
                    <= s1.compounds.len()
                &&& s1.complexes[i].combinators.lo <= s1.complexes[i].combinators.hi
                    <= s1.combinators.len()
            } by {
                if i < lo {
                    assert(s1.complexes[i] == s0.complexes[i]);
                } else {
                    assert(s1.complexes[i] == cs[i - lo]);
                    assert(complex_in(s0, cs[i - lo]));
                }
            }
            assert forall|i: int| 0 <= i < s1.lists.len() implies #[trigger] s1.lists[i].lo <= s1.lists[i].hi
                <= s1.complexes.len() by {
                if i < s0.lists.len() {
                    assert(s1.lists[i] == s0.lists[i]);
                }
            }
        }
        assert(refs_lt(s1)) by {
            assert forall|si: int| 0 <= si < s1.simples.len() implies #[trigger] ref_lt(
                s1.simples[si],
                s1.lists.len() as int,
            ) by {
                assert(s1.simples[si] == s0.simples[si]);
                assert(ref_lt(s0.simples[si], s0.lists.len() as int));
            }
        }
        // The list's complex selectors are the pending ones.
        reveal(pv_complexes);
        lemma_view_complexes(s1, r as int, lo as int, hi as int);
        assert forall|k: int| 0 <= k < cs.len() implies view_complexes(s1, r as int, lo as int, hi as int)[k]
            == pv_complexes(s0, cs)[k] by {
            assert(s1.complexes[lo + k] == cs[k]);
            lemma_view_complex_is(s1, r as int, lo + k);
            lemma_stable_complex(s0, s1, r as int, cs[k]);
        }
        assert(view_list(s1, r as int) =~= pv_complexes(s0, cs));
    }
    r
}

/// [`functional_pseudo_class`]: `name(` the rows `lo` up to `hi` `)`.
fn functional_pseudo_class_of(
    src: &ExecParsed,
    name: &[u32],
    lo: usize,
    hi: usize,
    out: &mut Build,
    depth: usize,
) -> (r: Option<ExecSimple>)
    requires
        src_ok(*src),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r is Some ==> ref_lt(r.unwrap(), final(out).selectors.lists.len() as int),
        final(out).too_deep || match r {
            Some(e) => functional_pseudo_class(name@, rows_list(*src, lo as int, hi as int)) == Some(
                view_exec_simple(final(out).selectors, final(out).selectors.lists.len() as int, e),
            ),
            None => functional_pseudo_class(name@, rows_list(*src, lo as int, hi as int)) is None,
        },
        (!old(out).too_deep && depth >= 1 && depth_ok(rows_list(*src, lo as int, hi as int), depth as int - 1))
            ==> !final(out).too_deep,
    decreases depth, 0int,
{
    if depth == 0 {
        out.too_deep = true;
        return None;
    }
    let inner = depth.saturating_sub(1);
    let ghost l = rows_list(*src, lo as int, hi as int);
    let ghost out0 = *out;
    if matches_ignoring_case(name, &[0x69, 0x73]) {
        let value = read_items(src, lo, hi);
        let list = forgiving_list_of(src, value.as_slice(), out, inner);
        proof {
            assert(ascii_case_insensitive_match(name@, str_is()));
            if !out.too_deep {
                assert(view_items(*src, value@) == l);
                assert(list < out.selectors.lists.len());
            }
        }
        Some(ExecSimple::Is { list })
    } else if matches_ignoring_case(name, &[0x77, 0x68, 0x65, 0x72, 0x65]) {
        let value = read_items(src, lo, hi);
        let list = forgiving_list_of(src, value.as_slice(), out, inner);
        proof {
            assert(ascii_case_insensitive_match(name@, str_where()));
            assert(!ascii_case_insensitive_match(name@, str_is()));
            if !out.too_deep {
                assert(view_items(*src, value@) == l);
                assert(list < out.selectors.lists.len());
            }
        }
        Some(ExecSimple::Where { list })
    } else if matches_ignoring_case(name, &[0x6E, 0x6F, 0x74]) {
        let value = read_items(src, lo, hi);
        let value = value.as_slice();
        let list = complex_list_of(src, value, 0, value.len(), true, out, inner);
        proof {
            assert(ascii_case_insensitive_match(name@, str_not()));
            assert(!ascii_case_insensitive_match(name@, str_is()));
            assert(!ascii_case_insensitive_match(name@, str_where()));
        }
        match list {
            Some(list) => Some(ExecSimple::Not { list }),
            None => None,
        }
    } else {
        proof {
            assert(!ascii_case_insensitive_match(name@, str_is()));
            assert(!ascii_case_insensitive_match(name@, str_where()));
            assert(!ascii_case_insensitive_match(name@, str_not()));
        }
        let kind = match nth_of(name) {
            Some(k) => k,
            None => {
                return None;
            },
        };
        let (a, b) = match a_n_plus_b_of(src, lo, hi) {
            Some(t) => t,
            None => {
                return None;
            },
        };
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
) -> (r: Found<ExecSimple>)
    requires
        src_ok(*src),
        hi <= items.len(),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r is Here ==> ref_lt(r->Here_0, final(out).selectors.lists.len() as int),
        final(out).too_deep || match r {
            Found::Absent => subclass_selector(view_items(*src, items@), i as int, hi as int) is Absent,
            Found::Invalid => subclass_selector(view_items(*src, items@), i as int, hi as int) is Invalid,
            Found::Here(e, n) => subclass_selector(view_items(*src, items@), i as int, hi as int)
                == (Step::Found {
                value: view_exec_simple(final(out).selectors, final(out).selectors.lists.len() as int, e),
                next: n as int,
            }),
        },
        (!old(out).too_deep && depth_ok(view_items(*src, items@), depth as int)) ==> !final(out).too_deep,
    decreases depth, 1int,
{
    let ghost l = view_items(*src, items@);
    if i >= hi || i >= items.len() {
        return Found::Absent;
    }
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    proof {
        assert(l[i as int] == item_view(*src, items@[i as int]));
    }
    match item(items, i) {
        ExecItem::Token { token: ExecToken::Hash { value, is_id } } => if *is_id {
            Found::Here(ExecSimple::Id { name: copy(value) }, i1)
        } else {
            Found::Invalid
        },
        ExecItem::Token { token: ExecToken::Delim { value: 0x2E } } => match ident(src, items, i1, hi) {
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
            if is_colon(src, items, i1, hi) {
                return Found::Absent;
            }
            if i1 >= hi || i1 >= items.len() {
                return Found::Invalid;
            }
            proof {
                assert(l[i1 as int] == item_view(*src, items@[i1 as int]));
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
                ExecItem::Function { name, lo, hi: end } => {
                    proof {
                        if depth_ok(l, depth as int) {
                            lemma_fn_depth(l, depth as int, i1 as int);
                        }
                    }
                    match functional_pseudo_class_of(src, name, *lo, *end, out, depth) {
                        Some(simple) => Found::Here(simple, i2),
                        None => Found::Invalid,
                    }
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
) -> (r: Option<(Vec<ExecSimple>, usize)>)
    requires
        src_ok(*src),
        hi <= items.len(),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r is Some ==> acc_in(final(out).selectors, r.unwrap().0@),
        final(out).too_deep || match r {
            Some((acc, n)) => compound_selector(
                view_items(*src, items@),
                i as int,
                hi as int,
                no_pseudo,
            ) == Some((pv_seq(final(out).selectors, acc@), n as int)),
            None => compound_selector(view_items(*src, items@), i as int, hi as int, no_pseudo) is None,
        },
        (!old(out).too_deep && depth_ok(view_items(*src, items@), depth as int)) ==> !final(out).too_deep,
    decreases depth, 2int,
{
    let ghost l = view_items(*src, items@);
    let ghost out0 = *out;
    let mut acc: Vec<ExecSimple> = Vec::new();
    if i > hi {
        proof {
            lemma_pv_push(out.selectors, Seq::empty(), ExecSimple::Universal { ns: NsPrefix::Absent });
            assert(acc@ =~= Seq::<ExecSimple>::empty());
            assert(subclass_selector(l, i as int, hi as int) is Absent);
            assert(pseudo_element(l, i as int, hi as int) is Absent);
        }
        return Some((acc, i));
    }
    let mut j = match type_selector_at(src, items, i, hi) {
        Found::Invalid => {
            return None;
        },
        Found::Absent => i,
        Found::Here(value, next) => {
            if !(i < next && next <= hi) {
                return None;
            }
            proof {
                lemma_pv_push(out.selectors, acc@, value);
                assert(plain(value));
            }
            acc.push(value);
            next
        },
    };
    proof {
        assert(out0 == *out);
        match type_selector(l, i as int, hi as int) {
            Step::Absent => {
                lemma_pv_push(out.selectors, Seq::empty(), ExecSimple::Universal { ns: NsPrefix::Absent });
                assert(acc@ =~= Seq::<ExecSimple>::empty());
            },
            Step::Found { value, next } => {
                assert(acc@.len() == 1);
                lemma_pv_push(out.selectors, Seq::empty(), acc@[0]);
                assert(acc@ =~= seq![acc@[0]]);
            },
            Step::Invalid => {},
        }
    }
    loop
        invariant
            j <= hi,
            hi <= items.len(),
            l == view_items(*src, items@),
            src_ok(*src),
            out0 == *old(out),
            step_ok(out0, *out),
            acc_in(out.selectors, acc@),
            (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
            out.too_deep || compound_selector(l, i as int, hi as int, no_pseudo) == subclass_selectors(
                l,
                j as int,
                hi as int,
                pv_seq(out.selectors, acc@),
                no_pseudo,
            ),
        decreases hi - j,
    {
        let ghost s_before = out.selectors;
        let ghost acc_before = acc@;
        match subclass_selector_at(src, items, j, hi, out, depth) {
            Found::Invalid => {
                return None;
            },
            Found::Here(value, next) => {
                if !(j < next && next <= hi) {
                    return None;
                }
                proof {
                    lemma_pv_stable(s_before, out.selectors, acc@);
                    lemma_pv_push(out.selectors, acc@, value);
                }
                acc.push(value);
                j = next;
            },
            Found::Absent => {
                proof {
                    lemma_pv_stable(s_before, out.selectors, acc@);
                }
                let ghost s_now = out.selectors;
                let end = match pseudo_compound_at(src, items, j, hi, &mut acc, no_pseudo, Ghost(s_now)) {
                    Some(end) => end,
                    None => {
                        return None;
                    },
                };
                return Some((acc, end));
            },
        }
    }
}

/// [`complex_selector`] on `lo` up to `hi`, with [`complex_selector_loop`] as its loop: the
/// complex selector, its compounds and combinators appended to the arrays.
#[verifier::spinoff_prover]
fn complex_selector_of(
    src: &ExecParsed,
    items: &[ExecItem],
    lo: usize,
    hi: usize,
    no_pseudo: bool,
    out: &mut Build,
    depth: usize,
) -> (r: Option<ExecComplex>)
    requires
        src_ok(*src),
        hi <= items.len(),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r is Some ==> complex_in(final(out).selectors, r.unwrap()),
        final(out).too_deep || match r {
            Some(c) => complex_selector(
                view_items(*src, items@),
                lo as int,
                hi as int,
                no_pseudo,
            ) == Some(pv_complex(final(out).selectors, c)),
            None => complex_selector(view_items(*src, items@), lo as int, hi as int, no_pseudo) is None,
        },
        (!old(out).too_deep && depth_ok(view_items(*src, items@), depth as int)) ==> !final(out).too_deep,
    decreases depth, 3int,
{
    let ghost l = view_items(*src, items@);
    let ghost out0 = *out;
    let start = skip_ws(src, items, lo, hi);
    if start >= hi || start < lo {
        return None;
    }
    let mut compounds: Vec<ExecRange> = Vec::new();
    let mut combinators: Vec<Combinator> = Vec::new();
    let mut i = start;
    proof {
        assert(compounds@ =~= Seq::<ExecRange>::empty());
        lemma_pvs_push(out.selectors, Seq::empty(), ExecRange { lo: 0, hi: 0 });
    }
    loop
        invariant_except_break
            i < hi,
            hi <= items.len(),
            l == view_items(*src, items@),
            src_ok(*src),
            start < hi,
            start == skip_whitespace(l, lo as int, hi as int),
            out0 == *old(out),
            step_ok(out0, *out),
            ranges_in(out.selectors, compounds@),
            (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
            out.too_deep || complex_selector(l, lo as int, hi as int, no_pseudo) == complex_selector_loop(
                l,
                i as int,
                hi as int,
                pv_compounds(out.selectors, compounds@),
                combinators@,
                no_pseudo,
            ),
        ensures
            step_ok(out0, *out),
            ranges_in(out.selectors, compounds@),
            (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
            out.too_deep || complex_selector(l, lo as int, hi as int, no_pseudo) == Some(
                Complex { compounds: pv_compounds(out.selectors, compounds@), combinators: combinators@ },
            ),
        decreases hi - i,
    {
        let ghost s0 = out.selectors;
        let ghost rs0 = compounds@;
        let ghost ks0 = combinators@;
        let (compound, next) = match compound_selector_at(src, items, i, hi, no_pseudo, out, depth) {
            Some(t) => t,
            None => {
                proof {
                    if !out.too_deep {
                        lemma_cs_fails(l, i as int, hi as int, pv_compounds(s0, rs0), ks0, no_pseudo);
                    }
                }
                return None;
            },
        };
        let ghost s1 = out.selectors;
        proof {
            lemma_stable_pv_compounds(s0, s1, rs0);
        }
        if next <= i || next > hi {
            proof {
                if !out.too_deep {
                    lemma_cs_fails(l, i as int, hi as int, pv_compounds(s0, rs0), ks0, no_pseudo);
                }
            }
            return None;
        }
        let pseudo = holds_pseudo_element(compound.as_slice(), Ghost(s1));
        let first = out.selectors.simples.len();
        let mut compound = compound;
        let ghost cv = compound@;
        out.selectors.simples.append(&mut compound);
        let end = out.selectors.simples.len();
        compounds.push(ExecRange { lo: first, hi: end });
        let ghost s2 = out.selectors;
        proof {
            let ghost g = s2;
            axiom_lengths(&g);
            lemma_append_compound(s1, s2, cv);
            lemma_compounds_push(s0, s1, s2, rs0, ExecRange { lo: first, hi: end }, cv);
            lemma_grows_trans(s0, s1, s2);
            lemma_pvs_push(s0, rs0, ExecRange { lo: first, hi: end });
        }
        let after = skip_ws(src, items, next, hi);
        let ghost cmp = pv_seq(s1, cv);
        if after >= hi {
            proof {
                if !out.too_deep {
                    lemma_cs_end(l, i as int, hi as int, pv_compounds(s0, rs0), ks0, no_pseudo, cmp, next as int);
                }
            }
            break;
        }
        if pseudo {
            proof {
                if !out.too_deep {
                    lemma_cs_pseudo(l, i as int, hi as int, pv_compounds(s0, rs0), ks0, no_pseudo, cmp, next as int);
                }
            }
            return None;
        }
        match combinator_of(src, items, after, hi) {
            Some(combinator) => {
                let begin = skip_ws(src, items, after.saturating_add(1), hi);
                proof {
                    if !out.too_deep {
                        lemma_cs_combinator(
                            l,
                            i as int,
                            hi as int,
                            pv_compounds(s0, rs0),
                            ks0,
                            no_pseudo,
                            cmp,
                            next as int,
                            combinator,
                        );
                    }
                }
                if begin >= hi || begin <= i {
                    return None;
                }
                combinators.push(combinator);
                i = begin;
            },
            None => {
                proof {
                    if !out.too_deep {
                        lemma_cs_descendant(
                            l,
                            i as int,
                            hi as int,
                            pv_compounds(s0, rs0),
                            ks0,
                            no_pseudo,
                            cmp,
                            next as int,
                        );
                    }
                }
                if after > next {
                    combinators.push(Combinator::Descendant);
                    i = after;
                } else {
                    return None;
                }
            },
        }
    }
    let ghost s2 = out.selectors;
    let ghost rs = compounds@;
    let ghost ks = combinators@;
    let c_lo = out.selectors.compounds.len();
    out.selectors.compounds.append(&mut compounds);
    let c_hi = out.selectors.compounds.len();
    let k_lo = out.selectors.combinators.len();
    out.selectors.combinators.append(&mut combinators);
    let k_hi = out.selectors.combinators.len();
    let r = ExecComplex {
        compounds: ExecRange { lo: c_lo, hi: c_hi },
        combinators: ExecRange { lo: k_lo, hi: k_hi },
    };
    proof {
        let s3 = out.selectors;
        let ghost g = s3;
        axiom_lengths(&g);
        lemma_append_complex(s2, s3, rs, ks);
        lemma_grows_trans(out0.selectors, s2, s3);
    }
    Some(r)
}

/// [`complex_list`] on `lo` up to `hi`: the index of the list, appended to the arrays.
#[verifier::spinoff_prover]
fn complex_list_of(
    src: &ExecParsed,
    items: &[ExecItem],
    lo: usize,
    hi: usize,
    no_pseudo: bool,
    out: &mut Build,
    depth: usize,
) -> (r: Option<usize>)
    requires
        src_ok(*src),
        hi <= items.len(),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r is Some ==> r.unwrap() + 1 == final(out).selectors.lists.len(),
        final(out).too_deep || match r {
            Some(li) => complex_list(
                view_items(*src, items@),
                lo as int,
                hi as int,
                no_pseudo,
            ) == Some(view_list(final(out).selectors, li as int)),
            None => complex_list(view_items(*src, items@), lo as int, hi as int, no_pseudo) is None,
        },
        (!old(out).too_deep && depth_ok(view_items(*src, items@), depth as int)) ==> !final(out).too_deep,
    decreases depth, 4int,
{
    let ghost l = view_items(*src, items@);
    let ghost out0 = *out;
    let mut complexes: Vec<ExecComplex> = Vec::new();
    if lo > hi {
        proof {
            lemma_cl_past(l, lo as int, hi as int, Seq::empty(), no_pseudo);
        }
        return None;
    }
    let mut i = lo;
    proof {
        assert(complexes@ =~= Seq::<ExecComplex>::empty());
        lemma_pvc_push(out.selectors, Seq::empty(), ExecComplex {
            compounds: ExecRange { lo: 0, hi: 0 },
            combinators: ExecRange { lo: 0, hi: 0 },
        });
    }
    loop
        invariant_except_break
            i <= hi,
            hi <= items.len(),
            lo <= i,
            l == view_items(*src, items@),
            src_ok(*src),
            out0 == *old(out),
            step_ok(out0, *out),
            cs_in(out.selectors, complexes@),
            (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
            out.too_deep || complex_list(l, lo as int, hi as int, no_pseudo) == complex_list_loop(
                l,
                i as int,
                hi as int,
                pv_complexes(out.selectors, complexes@),
                no_pseudo,
            ),
        ensures
            step_ok(out0, *out),
            cs_in(out.selectors, complexes@),
            (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
            out.too_deep || complex_list(l, lo as int, hi as int, no_pseudo) == Some(
                pv_complexes(out.selectors, complexes@),
            ),
        decreases hi - i,
    {
        let ghost s0 = out.selectors;
        let ghost cs0 = complexes@;
        let comma = next_comma_at(src, items, i, hi);
        let selector = complex_selector_of(src, items, i, comma, no_pseudo, out, depth);
        proof {
            lemma_pvc_stable(s0, out.selectors, cs0);
            if !out.too_deep {
                lemma_cl_step(
                    l,
                    i as int,
                    hi as int,
                    pv_complexes(s0, cs0),
                    no_pseudo,
                    match selector {
                        Some(c) => Some(pv_complex(out.selectors, c)),
                        None => None,
                    },
                );
            }
        }
        let selector = match selector {
            Some(c) => c,
            None => {
                return None;
            },
        };
        complexes.push(selector);
        proof {
            lemma_pvc_push(out.selectors, cs0, selector);
            assert(complexes@.drop_last() =~= cs0);
            assert forall|k: int| 0 <= k < complexes@.len() implies complex_in(out.selectors, complexes@[k]) by {
                if k < cs0.len() {
                    assert(complexes@[k] == cs0[k]);
                }
            }
        }
        if comma >= hi {
            break;
        }
        i = comma.saturating_add(1);
    }
    let idx = push_list(out, complexes);
    Some(idx)
}

/// [`parse_as_a_forgiving_selector_list`] on all of `items`: the index of the list.
#[verifier::spinoff_prover]
fn forgiving_list_of(src: &ExecParsed, items: &[ExecItem], out: &mut Build, depth: usize) -> (r: usize)
    requires
        src_ok(*src),
        ranges_wf(old(out).selectors),
        refs_lt(old(out).selectors),
    ensures
        step_ok(*old(out), *final(out)),
        r + 1 == final(out).selectors.lists.len(),
        final(out).too_deep || parse_as_a_forgiving_selector_list(view_items(*src, items@)) == view_list(
            final(out).selectors,
            r as int,
        ),
        (!old(out).too_deep && depth_ok(view_items(*src, items@), depth as int)) ==> !final(out).too_deep,
    decreases depth, 4int,
{
    let ghost l = view_items(*src, items@);
    let ghost out0 = *out;
    let hi = items.len();
    let mut complexes: Vec<ExecComplex> = Vec::new();
    proof {
        assert(complexes@ =~= Seq::<ExecComplex>::empty());
        lemma_pvc_push(out.selectors, Seq::empty(), ExecComplex {
            compounds: ExecRange { lo: 0, hi: 0 },
            combinators: ExecRange { lo: 0, hi: 0 },
        });
        assert(l.len() == hi);
    }
    let first = skip_ws(src, items, 0, hi);
    if first < hi {
        let mut i: usize = 0;
        loop
            invariant_except_break
                i < hi,
                hi == items.len(),
                l == view_items(*src, items@),
                src_ok(*src),
                out0 == *old(out),
                step_ok(out0, *out),
                cs_in(out.selectors, complexes@),
                (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
                out.too_deep || parse_as_a_forgiving_selector_list(l) == forgiving_list_loop(
                    l,
                    i as int,
                    hi as int,
                    pv_complexes(out.selectors, complexes@),
                ),
            ensures
                step_ok(out0, *out),
                cs_in(out.selectors, complexes@),
                (out0.too_deep == false && depth_ok(l, depth as int)) ==> !out.too_deep,
                out.too_deep || parse_as_a_forgiving_selector_list(l) == pv_complexes(
                    out.selectors,
                    complexes@,
                ),
            decreases hi - i,
        {
            let ghost s0 = out.selectors;
            let ghost cs0 = complexes@;
            let comma = next_comma_at(src, items, i, hi);
            let selector = complex_selector_of(src, items, i, comma, true, out, depth);
            proof {
                lemma_pvc_stable(s0, out.selectors, cs0);
                if !out.too_deep {
                    lemma_fl_step(
                        l,
                        i as int,
                        hi as int,
                        pv_complexes(s0, cs0),
                        match selector {
                            Some(c) => Some(pv_complex(out.selectors, c)),
                            None => None,
                        },
                    );
                }
            }
            if let Some(selector) = selector {
                complexes.push(selector);
                proof {
                    lemma_pvc_push(out.selectors, cs0, selector);
                    assert(complexes@.drop_last() =~= cs0);
                    assert forall|k: int| 0 <= k < complexes@.len() implies complex_in(out.selectors, complexes@[k]) by {
                        if k < cs0.len() {
                            assert(complexes@[k] == cs0[k]);
                        }
                    }
                }
            }
            if comma >= hi {
                break;
            }
            i = comma.saturating_add(1);
            if i >= hi {
                proof {
                    if !out.too_deep {
                        lemma_fl_end(l, i as int, hi as int, pv_complexes(out.selectors, complexes@));
                    }
                }
                break;
            }
        }
    } else {
        proof {
            assert(only_whitespace(l, 0, hi as int));
        }
    }
    proof {
        if first >= hi {
            lemma_pvc_push(out.selectors, Seq::empty(), ExecComplex {
                compounds: ExecRange { lo: 0, hi: 0 },
                combinators: ExecRange { lo: 0, hi: 0 },
            });
        }
    }
    push_list(out, complexes)
}

/// The selectors a result stands for.
pub open spec fn view_result(r: Option<ExecSelectors>) -> Option<Seq<Complex>> {
    match r {
        Some(s) => Some(view_selectors(s)),
        None => None,
    }
}

/// §21.1 "parse a selector" from `input`: the selectors, whose result is the last list, or
/// `None` for failure, or if functions nest more deeply than
/// [`super::contract::MAX_NESTING`]. It meets [`parse_selector_ensures`], and what is returned
/// is [`super::exec_check::checked`].
pub fn parse_selector(input: &[u32]) -> (r: Option<ExecSelectors>)
    requires
        clazel_css::parser::contract::parser_input_requires(input@),
    ensures
        parse_selector_ensures(input@, view_result(r)),
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
    let ghost values = selector_values(input@);
    proof {
        assert(view_items(parsed, items@) == values);
        assert(ranges_wf(out.selectors));
        assert(refs_lt(out.selectors));
    }
    let result = complex_list_of(&parsed, items, 0, items.len(), false, &mut out, MAX_NESTING);
    proof {
        assert(selector_list(values) == complex_list(values, 0, values.len() as int, false));
        assert(parse_a_selector(input@) == selector_list(values));
        assert(items.len() == values.len());
    }
    match result {
        None => None,
        Some(li) => {
            let _ = li;
            if out.too_deep {
                None
            } else {
                proof {
                    theorem_parse_total(input@);
                    assert(view_selectors(out.selectors) == view_list(out.selectors, li as int));
                }
                Some(out.selectors)
            }
        },
    }
}

} // verus!
