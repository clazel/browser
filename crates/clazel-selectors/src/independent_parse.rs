//! Parsing: the independent transcription's parse of a selector list from component values
//! ([`super::independent::i_parse_selector_list`]) against the spec's
//! ([`super::spec::selector_list`]), on the selectors the two have in common.
//!
//! What the spec supports and the transcription does not (pseudo-elements, `:link`, `:visited`,
//! `:any-link`, the user action pseudo-classes) makes the two differ on some inputs, and what the
//! transcription supports and the spec does not (`:has()`, `:scope`, `:defined`, `of S`) is off
//! when [`ICtx::ext`] is false. So the theorems have two halves:
//!
//! - **spec to transcription**: if the spec parses a list to something the transcription has a
//!   counterpart for ([`rel_list`]), the transcription parses the same input to that
//!   counterpart;
//! - **transcription to spec**: if the transcription parses an input, so does the spec.
//!
//! Together: wherever the spec's result is made of selectors both support, the two agree; and the
//! transcription accepts nothing the spec rejects. The first half is false without a premise
//! about the input's end: a compound selector stops at white space, a combinator or the end,
//! and the spec's compound parser can also stop at a stray token that its caller then rejects.

#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::independent_equivalence::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The context the spec parses in: no prefix declared, no default namespace, and none of the
/// selectors the spec does not support.
pub open spec fn cx0() -> ICtx {
    ICtx { default_ns: None, decls: Map::empty(), ext: false }
}

// ------------------------------------------------------------------------------------
// Reading items: the spec's guarded readers are the transcription's
// ------------------------------------------------------------------------------------

/// The identifier at `i`.
pub proof fn lemma_ident_at(v: Seq<ComponentValue>, i: int, hi: int)
    requires
        hi <= v.len(),
    ensures
        ident_at(v, i, hi) == if 0 <= i < hi {
            i_ident(v[i])
        } else {
            None
        },
{
}

/// The delimiter at `i`.
pub proof fn lemma_delim_at(v: Seq<ComponentValue>, i: int, hi: int, c: u32)
    requires
        hi <= v.len(),
    ensures
        is_delim_at(v, i, hi, c) == (0 <= i < hi && i_is_delim(v[i], c)),
{
}

/// The colon at `i`.
pub proof fn lemma_colon_at(v: Seq<ComponentValue>, i: int, hi: int)
    requires
        hi <= v.len(),
    ensures
        is_token_at(v, i, hi, Token::Colon) == (0 <= i < hi && i_is_colon(v[i])),
{
}

/// The spec's run of white space is the transcription's skip.
pub proof fn lemma_skip_same(v: Seq<ComponentValue>, i: int, hi: int)
    requires
        0 <= i,
        hi <= v.len(),
    ensures
        skip_whitespace(v, i, hi) == i_skip_ws(v, i, hi),
    decreases hi - i,
{
    if i < hi && i_is_ws(v[i]) {
        lemma_skip_same(v, i + 1, hi);
        assert(whitespace_run(v, i, hi) == 1 + whitespace_run(v, i + 1, hi));
    }
}

/// The combinator at `i`.
pub proof fn lemma_combinator_at(v: Seq<ComponentValue>, i: int, hi: int)
    requires
        hi <= v.len(),
    ensures
        match combinator_at(v, i, hi) {
            Some(c) => 0 <= i < hi && i_comb_of(v[i]) is Some && rel_comb(c, i_comb_of(v[i]).unwrap()),
            None => !(0 <= i < hi) || i_comb_of(v[i]) is None,
        },
{
}

/// The spec's search for a comma is the transcription's.
pub proof fn lemma_comma_same(v: Seq<ComponentValue>, i: int, hi: int)
    requires
        0 <= i,
        hi <= v.len(),
    ensures
        i <= hi ==> next_comma(v, i, hi) == i_comma(v, i, hi),
    decreases hi - i,
{
    if i < hi && !i_is_comma(v[i]) {
        lemma_comma_same(v, i + 1, hi);
    }
}

// ------------------------------------------------------------------------------------
// Type selectors
// ------------------------------------------------------------------------------------

/// `<type-selector>`: the two read the same, and say the same of what they found.
pub proof fn lemma_type_selector(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p,
        end <= v.len(),
    ensures
        match type_selector(v, p, end) {
            Step::Invalid => i_type_selector(v, p, end, cx0()) is None,
            Step::Absent => i_type_selector(v, p, end, cx0()) == Some::<Option<(IType, int)>>(None),
            Step::Found { value, next } => match i_type_selector(v, p, end, cx0()) {
                Some(Some((t, q))) => q == next && rel_type(value, t),
                _ => false,
            },
        },
{
    lemma_ident_at(v, p, end);
    lemma_ident_at(v, p + 1, end);
    lemma_ident_at(v, p + 2, end);
    lemma_delim_at(v, p, end, 0x2A);
    lemma_delim_at(v, p + 1, end, 0x7C);
    lemma_delim_at(v, p + 2, end, 0x2A);
    lemma_delim_at(v, p, end, 0x7C);
}

// ------------------------------------------------------------------------------------
// Attribute selectors
// ------------------------------------------------------------------------------------

/// The string or identifier that is an attribute selector's value.
pub proof fn lemma_attr_value(b: Seq<ComponentValue>, r: int)
    requires
        0 <= r,
    ensures
        (match token_at(b, r, b.len() as int) {
            Some(Token::String { value }) => Some(value),
            Some(Token::Ident { value }) => Some(value),
            _ => None,
        }) == if 0 <= r < b.len() {
            if i_ident(b[r]) is Some {
                i_ident(b[r])
            } else {
                i_string(b[r])
            }
        } else {
            None
        },
{
}

/// `<attr-matcher>`.
pub proof fn lemma_attr_matcher(b: Seq<ComponentValue>, q: int)
    requires
        0 <= q,
    ensures
        match attr_matcher(b, q) {
            Some((m, next)) => match i_attr_matcher(b, q) {
                Some((op, next2)) => next == next2 && rel_matcher(m, op),
                None => false,
            },
            None => i_attr_matcher(b, q) is None,
        },
{
    let hi = b.len() as int;
    lemma_delim_at(b, q, hi, 0x3D);
    lemma_delim_at(b, q + 1, hi, 0x3D);
    lemma_delim_at(b, q, hi, 0x7E);
    lemma_delim_at(b, q, hi, 0x7C);
    lemma_delim_at(b, q, hi, 0x5E);
    lemma_delim_at(b, q, hi, 0x24);
    lemma_delim_at(b, q, hi, 0x2A);
}

/// `<wq-name>` of an attribute selector: where the transcription finds a name, the spec finds
/// the same; where the spec finds one the transcription does not, a `|` follows it that is not
/// the start of `|=`.
pub proof fn lemma_attr_name(b: Seq<ComponentValue>, i: int)
    requires
        0 <= i,
    ensures
        match attribute_name(b, i) {
            Some((_, _, next)) => next <= b.len() && next > i,
            None => true,
        },
        match i_attr_name(b, i, cx0()) {
            Some((m, name, next)) => match attribute_name(b, i) {
                Some((ns, name2, next2)) => next == next2 && name == name2 && rel_ns_attr(ns, m),
                None => false,
            },
            None => match attribute_name(b, i) {
                Some((_, _, next)) => 0 <= next < b.len() && i_is_delim(b[next], 0x7C) && !(next + 1
                    < b.len() && i_is_delim(b[next + 1], 0x3D)),
                None => true,
            },
        },
{
    let hi = b.len() as int;
    lemma_ident_at(b, i, hi);
    lemma_ident_at(b, i + 1, hi);
    lemma_ident_at(b, i + 2, hi);
    lemma_delim_at(b, i, hi, 0x2A);
    lemma_delim_at(b, i, hi, 0x7C);
    lemma_delim_at(b, i + 1, hi, 0x7C);
    lemma_delim_at(b, i + 2, hi, 0x3D);
}

/// The part of an attribute selector after its name.
pub proof fn lemma_attr_rest(b: Seq<ComponentValue>, ns: NsPrefix, name: Seq<u32>, after: int, m: INs)
    requires
        0 <= after <= b.len(),
        rel_ns_attr(ns, m),
        attribute_name(b, i_skip_ws(b, 0, b.len() as int)) == Some((ns, name, after)),
        match i_attr_name(b, i_skip_ws(b, 0, b.len() as int), cx0()) {
            Some((m2, name2, after2)) => m2 == m && name2 == name && after2 == after,
            None => false,
        },
    ensures
        match attribute_selector(b) {
            Some(Simple::Attribute { ns: ns2, name: name2, test }) => match i_attribute_selector(
                b,
                cx0(),
            ) {
                Some(a) => rel_attr(ns2, name2, test, a),
                None => false,
            },
            Some(_) => false,
            None => i_attribute_selector(b, cx0()) is None,
        },
{
    let hi = b.len() as int;
    lemma_skip_same(b, 0, hi);
    lemma_skip_same(b, after, hi);
    lemma_skip_ws(b, after, hi);
    let q = i_skip_ws(b, after, hi);
    if q < hi {
        lemma_attr_matcher(b, q);
        if let Some((mt, after_m)) = attr_matcher(b, q) {
            lemma_skip_same(b, after_m, hi);
            lemma_skip_ws(b, after_m, hi);
            let r = i_skip_ws(b, after_m, hi);
            lemma_attr_value(b, r);
            lemma_skip_same(b, r + 1, hi);
            if r < hi {
                lemma_skip_ws(b, r + 1, hi);
            }
            let s2 = i_skip_ws(b, r + 1, hi);
            lemma_ident_at(b, s2, hi);
            lemma_skip_same(b, s2 + 1, hi);
            if s2 < hi {
                lemma_skip_ws(b, s2 + 1, hi);
            }
            lemma_flag_names();
            if s2 < hi {
                if let Some(mm) = i_ident(b[s2]) {
                    lemma_ci_flag(mm);
                }
            }
        }
    }
}

/// The names `i` and `s`, as the spec and the transcription compare them.
pub proof fn lemma_ci_flag(mm: Seq<u32>)
    ensures
        ascii_case_insensitive_match(mm, seq![0x69u32]) == i_ci_eq(mm, seq![0x69u32]),
        ascii_case_insensitive_match(mm, seq![0x73u32]) == i_ci_eq(mm, seq![0x73u32]),
{
    lemma_ci_match_lower(mm, seq![0x69u32]);
    lemma_ci_match_lower(mm, seq![0x73u32]);
}

/// No code point of the literal is an upper-case letter.
pub open spec fn all_lc(lit: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < lit.len() ==> !(0x41 <= #[trigger] lit[k] <= 0x5A)
}

/// The spec's case-insensitive match against a lower-case literal is the transcription's.
pub proof fn lemma_ci_match_lower(s: Seq<u32>, lit: Seq<u32>)
    requires
        all_lc(lit),
    ensures
        ascii_case_insensitive_match(s, lit) == i_ci_eq(s, lit),
{
    if s.len() == lit.len() {
        lemma_matches_from(s, lit, 0);
        assert(forall|k: int| 0 <= k < lit.len() ==> i_lower(#[trigger] lit[k]) == lit[k]);
        if i_ci_eq(s, lit) {
            assert forall|k: int| 0 <= k < s.len() implies ascii_lowercase(#[trigger] s[k]) == lit[k] by {
                assert(i_lower(s[k]) == i_lower(lit[k]));
            }
        }
        if ascii_case_insensitive_match(s, lit) {
            assert forall|k: int| 0 <= k < s.len() implies i_lower(#[trigger] s[k]) == i_lower(lit[k]) by {
                assert(ascii_lowercase(s[k]) == lit[k]);
            }
        }
    }
}

/// The spec's `matches_from` is a quantifier.
pub proof fn lemma_matches_from(s: Seq<u32>, lit: Seq<u32>, i: int)
    requires
        0 <= i,
        s.len() == lit.len(),
    ensures
        matches_from(s, lit, i) == forall|k: int| i <= k < s.len() ==> ascii_lowercase(#[trigger] s[k]) == lit[k],
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_matches_from(s, lit, i + 1);
    }
}

/// `i` and `s` are lower-case.
pub proof fn lemma_flag_names()
    ensures
        all_lc(seq![0x69u32]),
        all_lc(seq![0x73u32]),
{
}

/// `<attribute-selector>`: the same attribute selector, or neither.
pub proof fn lemma_attribute_selector(b: Seq<ComponentValue>)
    ensures
        match attribute_selector(b) {
            Some(Simple::Attribute { ns, name, test }) => match i_attribute_selector(b, cx0()) {
                Some(a) => rel_attr(ns, name, test, a),
                None => false,
            },
            Some(_) => false,
            None => i_attribute_selector(b, cx0()) is None,
        },
{
    let hi = b.len() as int;
    lemma_skip_same(b, 0, hi);
    let start = i_skip_ws(b, 0, hi);
    lemma_attr_name(b, start);
    if let Some((ns, name, after)) = attribute_name(b, start) {
        match i_attr_name(b, start, cx0()) {
            Some((m, name2, after2)) => {
                lemma_attr_rest(b, ns, name, after, m);
            },
            None => {
                // The spec's name is followed by a `|` that does not begin `|=`: no matcher.
                lemma_skip_same(b, after, hi);
                assert(i_skip_ws(b, after, hi) == after);
                lemma_attr_matcher(b, after);
                lemma_delim_at(b, after, hi, 0x3D);
                lemma_delim_at(b, after + 1, hi, 0x3D);
            },
        }
    }
}


// ------------------------------------------------------------------------------------
// Pseudo-classes without arguments
// ------------------------------------------------------------------------------------

/// `focus` is not `focus-visible` or `focus-within`.
pub proof fn lemma_focus_names()
    ensures
        pseudo_class_name(PseudoClass::Focus) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Focus) != pseudo_class_name(PseudoClass::FocusWithin),
{
    assert(pseudo_class_name(PseudoClass::Focus).len() == 5);
    assert(pseudo_class_name(PseudoClass::FocusVisible).len() == 13);
    assert(pseudo_class_name(PseudoClass::FocusWithin).len() == 12);
}

/// No two pseudo-class names are the same.
pub proof fn lemma_class_names_distinct()
    ensures
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Visited),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::AnyLink),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Root),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Empty),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::FirstChild),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Link) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Link) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Link) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Link) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Link) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::AnyLink),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::Root),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::Empty),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::FirstChild),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Visited) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Visited) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Visited) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Visited) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Visited) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::Root),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::Empty),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::FirstChild),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::AnyLink) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::Empty),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::FirstChild),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Root) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Root) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Root) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Root) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Root) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::FirstChild),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Empty) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Empty) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Empty) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Empty) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Empty) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::LastChild),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::FirstChild) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::OnlyChild),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::LastChild) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::FirstOfType),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::OnlyChild) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::LastOfType),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::FirstOfType) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::OnlyOfType),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::LastOfType) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_class_name(PseudoClass::Hover),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::OnlyOfType) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Hover) != pseudo_class_name(PseudoClass::Active),
        pseudo_class_name(PseudoClass::Hover) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Hover) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Hover) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Hover) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Hover) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Hover) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Hover) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Active) != pseudo_class_name(PseudoClass::Focus),
        pseudo_class_name(PseudoClass::Active) != pseudo_class_name(PseudoClass::FocusVisible),
        pseudo_class_name(PseudoClass::Active) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::Active) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Active) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Active) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Active) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::Focus) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::Focus) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::Focus) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::Focus) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::FocusVisible) != pseudo_class_name(PseudoClass::FocusWithin),
        pseudo_class_name(PseudoClass::FocusVisible) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::FocusVisible) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::FocusVisible) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::FocusVisible) != pseudo_element_name(PseudoElement::FirstLetter),
        pseudo_class_name(PseudoClass::FocusWithin) != pseudo_element_name(PseudoElement::Before),
        pseudo_class_name(PseudoClass::FocusWithin) != pseudo_element_name(PseudoElement::After),
        pseudo_class_name(PseudoClass::FocusWithin) != pseudo_element_name(PseudoElement::FirstLine),
        pseudo_class_name(PseudoClass::FocusWithin) != pseudo_element_name(PseudoElement::FirstLetter),
{
}

/// The names are lower case.
pub proof fn lemma_names_lc()
    ensures
        all_lc(pseudo_class_name(PseudoClass::Link)),
        all_lc(pseudo_class_name(PseudoClass::Visited)),
        all_lc(pseudo_class_name(PseudoClass::AnyLink)),
        all_lc(pseudo_class_name(PseudoClass::Root)),
        all_lc(pseudo_class_name(PseudoClass::Empty)),
        all_lc(pseudo_class_name(PseudoClass::FirstChild)),
        all_lc(pseudo_class_name(PseudoClass::LastChild)),
        all_lc(pseudo_class_name(PseudoClass::OnlyChild)),
        all_lc(pseudo_class_name(PseudoClass::FirstOfType)),
        all_lc(pseudo_class_name(PseudoClass::LastOfType)),
        all_lc(pseudo_class_name(PseudoClass::OnlyOfType)),
        all_lc(pseudo_class_name(PseudoClass::Hover)),
        all_lc(pseudo_class_name(PseudoClass::Active)),
        all_lc(pseudo_class_name(PseudoClass::Focus)),
        all_lc(pseudo_class_name(PseudoClass::FocusVisible)),
        all_lc(pseudo_class_name(PseudoClass::FocusWithin)),
        all_lc(pseudo_element_name(PseudoElement::Before)),
        all_lc(pseudo_element_name(PseudoElement::After)),
        all_lc(pseudo_element_name(PseudoElement::FirstLine)),
        all_lc(pseudo_element_name(PseudoElement::FirstLetter)),
{
}

/// The spec's test of a name against each class's, as the transcription's.
pub proof fn lemma_class_tests(name: Seq<u32>)
    ensures
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Link)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Link)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Visited)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Visited)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::AnyLink)) == i_ci_eq(name, pseudo_class_name(PseudoClass::AnyLink)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Root)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Root)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Empty)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Empty)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FirstChild)) == i_ci_eq(name, pseudo_class_name(PseudoClass::FirstChild)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::LastChild)) == i_ci_eq(name, pseudo_class_name(PseudoClass::LastChild)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::OnlyChild)) == i_ci_eq(name, pseudo_class_name(PseudoClass::OnlyChild)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FirstOfType)) == i_ci_eq(name, pseudo_class_name(PseudoClass::FirstOfType)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::LastOfType)) == i_ci_eq(name, pseudo_class_name(PseudoClass::LastOfType)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::OnlyOfType)) == i_ci_eq(name, pseudo_class_name(PseudoClass::OnlyOfType)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Hover)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Hover)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Active)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Active)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Focus)) == i_ci_eq(name, pseudo_class_name(PseudoClass::Focus)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FocusVisible)) == i_ci_eq(name, pseudo_class_name(PseudoClass::FocusVisible)),
        ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FocusWithin)) == i_ci_eq(name, pseudo_class_name(PseudoClass::FocusWithin)),
        ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::Before)) == i_ci_eq(name, pseudo_element_name(PseudoElement::Before)),
        ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::After)) == i_ci_eq(name, pseudo_element_name(PseudoElement::After)),
        ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::FirstLine)) == i_ci_eq(name, pseudo_element_name(PseudoElement::FirstLine)),
        ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::FirstLetter)) == i_ci_eq(name, pseudo_element_name(PseudoElement::FirstLetter)),
{
    lemma_names_lc();
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Link));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Visited));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::AnyLink));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Root));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Empty));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::FirstChild));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::LastChild));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::OnlyChild));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::FirstOfType));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::LastOfType));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::OnlyOfType));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Hover));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Active));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::Focus));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::FocusVisible));
    lemma_ci_match_lower(name, pseudo_class_name(PseudoClass::FocusWithin));
    lemma_ci_match_lower(name, pseudo_element_name(PseudoElement::Before));
    lemma_ci_match_lower(name, pseudo_element_name(PseudoElement::After));
    lemma_ci_match_lower(name, pseudo_element_name(PseudoElement::FirstLine));
    lemma_ci_match_lower(name, pseudo_element_name(PseudoElement::FirstLetter));
}

/// A name matches at most one literal that is lower case.
pub proof fn lemma_ci_unique(name: Seq<u32>, l1: Seq<u32>, l2: Seq<u32>)
    requires
        all_lc(l1),
        all_lc(l2),
        i_ci_eq(name, l1),
        i_ci_eq(name, l2),
    ensures
        l1 == l2,
{
    assert(l1.len() == l2.len());
    assert forall|k: int| 0 <= k < l1.len() implies l1[k] == l2[k] by {
        assert(i_lower(name[k]) == i_lower(l1[k]));
        assert(i_lower(name[k]) == i_lower(l2[k]));
    }
    assert(l1 =~= l2);
}

/// The pseudo-classes without arguments, as the transcription reads them.
pub proof fn lemma_pseudo_ident(name: Seq<u32>)
    ensures
        // The transcription's class is the spec's, and its name is not a pseudo-element's.
        match i_pseudo_ident(name, cx0()) {
            Some(m) => pseudo_element_named(name) is None && match pseudo_class_named(name) {
                Some(c) => rel_simple(Simple::PseudoClass { class: c }, m),
                None => false,
            },
            None => true,
        },
        // Where the spec has a class with a transcription, that is the transcription's.
        forall|c: PseudoClass, m: ISimple|
            pseudo_class_named(name) == Some(c) && rel_simple(Simple::PseudoClass { class: c }, m) ==> {
                &&& pseudo_element_named(name) is None
                &&& i_pseudo_ident(name, cx0()) == Some(m)
            },
{
    lemma_class_tests(name);
    lemma_class_names_distinct();
    lemma_focus_names();
    lemma_names_lc();
}


// ------------------------------------------------------------------------------------
// One subclass selector
// ------------------------------------------------------------------------------------

/// What the two parsers do with a functional pseudo-class's name and arguments, which the proofs
/// about a list take for each function in it, and [`lemma_fun_prop`] proves of every one: where
/// the spec reads one that has a transcription, the transcription reads that; and where the
/// transcription reads one, the spec reads one too.
pub open spec fn fun_stmt_a(name: Seq<u32>, value: Seq<ComponentValue>, ih: bool, m: ISimple) -> bool {
    match functional_pseudo_class(name, value) {
        Some(s) => rel_simple(s, m) ==> i_pseudo_function(name, value, cx0(), ih) == Some(m),
        None => true,
    }
}

/// The second half of [`fun_stmt_a`]'s property.
pub open spec fn fun_stmt_b(name: Seq<u32>, value: Seq<ComponentValue>, ih: bool) -> bool {
    i_pseudo_function(name, value, cx0(), ih) is Some ==> functional_pseudo_class(name, value) is Some
}

/// Both halves, for every context. (Opaque, so that the proofs about lists do not unfold it.)
#[verifier::opaque]
pub open spec fn fun_prop(name: Seq<u32>, value: Seq<ComponentValue>) -> bool {
    (forall|ih: bool, m: ISimple| #[trigger] fun_stmt_a(name, value, ih, m)) && (forall|ih: bool|
        #[trigger] fun_stmt_b(name, value, ih))
}

/// Every function before `end` has the property.
pub open spec fn no_fun(v: Seq<ComponentValue>, end: int) -> bool {
    forall|k: int|
        0 <= k < end ==> (#[trigger] v[k] is Function ==> fun_prop(
            v[k]->Function_name,
            v[k]->Function_value,
        ))
}

/// A spec simple selector that is neither a pseudo-element nor a type or universal selector.
pub open spec fn sok(s: Simple) -> bool {
    !(s is PseudoElement) && !is_type_or_universal(s)
}

/// The spec's functional pseudo-classes are `:is()`, `:where()`, `:not()` or `:nth-*()`.
pub proof fn lemma_fpc_kind(name: Seq<u32>, value: Seq<ComponentValue>)
    ensures
        match functional_pseudo_class(name, value) {
            Some(s) => sok(s),
            None => true,
        },
{
    reveal_with_fuel(functional_pseudo_class, 2);
}

/// The position `q` is where a compound selector can end: at the end, white space or a
/// combinator.
pub open spec fn boundary(v: Seq<ComponentValue>, q: int, end: int) -> bool {
    q >= end || i_is_ws(v[q]) || i_comb_of(v[q]) is Some
}

/// The spec's step at a position where it finds a selector begins with something the
/// transcription's loop does not stop at.
pub proof fn lemma_sub_one_pre(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p < end <= v.len(),
    ensures
        match subclass_selector(v, p, end) {
            Step::Found { .. } => !i_is_ws(v[p]) && i_comb_of(v[p]) is None,
            _ => true,
        },
{
}

/// `<subclass-selector>`: what the transcription reads, the spec reads, to the same place.
pub proof fn lemma_sub_one_b(v: Seq<ComponentValue>, p: int, end: int, in_has: bool)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
    ensures
        match i_sub_one(v, p, end, cx0(), in_has) {
            Some((m, q)) => match subclass_selector(v, p, end) {
                Step::Found { value, next } => next == q && sok(value),
                _ => false,
            },
            None => true,
        },
{
    lemma_ident_at(v, p + 1, end);
    lemma_colon_at(v, p + 1, end);
    match v[p] {
        ComponentValue::SimpleBlock { associated_token: Token::OpenSquare, value } => {
            lemma_attribute_selector(value);
        },
        ComponentValue::Token { token: Token::Colon } => {
            if p + 1 < end {
                match v[p + 1] {
                    ComponentValue::Token { token: Token::Ident { value } } => {
                        lemma_pseudo_ident(value);
                    },
                    ComponentValue::Function { name, value } => {
                        reveal(fun_prop);
                        assert(fun_stmt_b(name, value, in_has));
                        lemma_fpc_kind(name, value);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

/// `<subclass-selector>`: what the spec reads and the transcription has a counterpart for, the
/// transcription reads.
pub proof fn lemma_sub_one_a(v: Seq<ComponentValue>, p: int, end: int, in_has: bool, m: ISimple)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
    ensures
        match subclass_selector(v, p, end) {
            Step::Found { value, next } => rel_simple(value, m) ==> i_sub_one(
                v,
                p,
                end,
                cx0(),
                in_has,
            ) == Some((m, next)),
            _ => true,
        },
{
    lemma_ident_at(v, p + 1, end);
    lemma_colon_at(v, p + 1, end);
    match v[p] {
        ComponentValue::SimpleBlock { associated_token: Token::OpenSquare, value } => {
            lemma_attribute_selector(value);
        },
        ComponentValue::Token { token: Token::Colon } => {
            if p + 1 < end {
                match v[p + 1] {
                    ComponentValue::Token { token: Token::Ident { value } } => {
                        lemma_pseudo_ident(value);
                    },
                    ComponentValue::Function { name, value } => {
                        reveal(fun_prop);
                        assert(fun_stmt_a(name, value, in_has, m));
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}


// ------------------------------------------------------------------------------------
// Runs of subclass selectors
// ------------------------------------------------------------------------------------

/// Simple selectors and their transcriptions, one for one.
pub open spec fn rel_simples(ss: Seq<Simple>, ms: Seq<ISimple>) -> bool {
    ss.len() == ms.len() && forall|k: int| 0 <= k < ss.len() ==> rel_simple(#[trigger] ss[k], ms[k])
}

/// Where the transcription's subclass selector ends.
pub proof fn lemma_sub_one_pos(v: Seq<ComponentValue>, p: int, end: int, in_has: bool)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
    ensures
        match i_sub_one(v, p, end, cx0(), in_has) {
            Some((_, q)) => p < q <= end,
            None => true,
        },
{
}

/// `<pseudo-class-selector>*` after a pseudo-element only adds to what was read.
pub proof fn lemma_user_actions_prefix(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>)
    ensures
        match user_actions(v, i, hi, acc) {
            Some((r, _)) => r.len() >= acc.len() && r.subrange(0, acc.len() as int) == acc,
            None => true,
        },
    decreases hi - i,
{
    match user_action(v, i, hi) {
        Step::Found { value, next } => {
            if next > i && next <= hi {
                lemma_user_actions_prefix(v, next, hi, acc.push(Simple::PseudoClass { class: value }));
                if let Some((r, _)) = user_actions(v, next, hi, acc.push(Simple::PseudoClass { class: value })) {
                    assert(r.subrange(0, acc.len() as int) =~= acc);
                }
            }
        },
        _ => {},
    }
}

/// What the spec's `<pseudo-compound-selector>` can add: nothing, or a pseudo-element, which the
/// transcription has no counterpart for.
pub proof fn lemma_pseudo_compound(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool)
    ensures
        match pseudo_compound(v, i, hi, acc, np) {
            Some((r, q)) => r.len() >= acc.len() && r.subrange(0, acc.len() as int) == acc && ((r == acc
                && q == i) || (r.len() > acc.len() && r[acc.len() as int] is PseudoElement)),
            None => true,
        },
{
    match pseudo_element(v, i, hi) {
        Step::Found { value, next } => {
            if !np {
                let acc1 = acc.push(Simple::PseudoElement { element: value });
                lemma_user_actions_prefix(v, next, hi, acc1);
                if let Some((r, _)) = user_actions(v, next, hi, acc1) {
                    assert(r.subrange(0, acc1.len() as int) == acc1);
                    assert(r[acc.len() as int] == acc1[acc.len() as int]);
                    assert(r.subrange(0, acc.len() as int) =~= acc);
                }
            }
        },
        _ => {},
    }
}

/// A run of subclass selectors extends what was read before.
pub proof fn lemma_subs_prefix(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool)
    ensures
        match subclass_selectors(v, i, hi, acc, np) {
            Some((r, _)) => r.len() >= acc.len() && r.subrange(0, acc.len() as int) == acc,
            None => true,
        },
    decreases hi - i,
{
    reveal_with_fuel(subclass_selectors, 2);
    match subclass_selector(v, i, hi) {
        Step::Found { value, next } => {
            if i < next && next <= hi {
                let acc2 = acc.push(value);
                lemma_subs_prefix(v, next, hi, acc2, np);
                if let Some((r, _)) = subclass_selectors(v, next, hi, acc2, np) {
                    assert(r.subrange(0, acc.len() as int) =~= acc);
                }
            }
        },
        Step::Absent => {
            lemma_pseudo_compound(v, i, hi, acc, np);
        },
        _ => {},
    }
}

/// The transcription's run of subclass selectors stops at a boundary.
pub proof fn lemma_i_subs_stop(v: Seq<ComponentValue>, p: int, end: int, in_has: bool, fuel: nat)
    requires
        0 <= p,
        fuel > 0,
        boundary(v, p, end),
    ensures
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((Seq::<ISimple>::empty(), p)),
{
    reveal_with_fuel(i_subs, 2);
}

/// The transcription's run of subclass selectors reads one and goes on.
pub proof fn lemma_i_subs_step(v: Seq<ComponentValue>, p: int, end: int, in_has: bool, fuel: nat, m: ISimple, next: int, ms1: Seq<ISimple>, q: int)
    requires
        0 <= p < end,
        fuel > 0,
        !boundary(v, p, end),
        i_sub_one(v, p, end, cx0(), in_has) == Some((m, next)),
        i_subs(v, next, end, cx0(), in_has, (fuel - 1) as nat) == Some((ms1, q)),
    ensures
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((seq![m] + ms1, q)),
{
    reveal_with_fuel(i_subs, 2);
}

/// The `j`-th transcribed simple selector is the counterpart of the `k + j`-th spec one. (Opaque, so
/// that the solver does not unfold every instance of the relation.)
#[verifier::opaque]
pub open spec fn relx(res: Seq<Simple>, k: int, ms: Seq<ISimple>, j: int) -> bool {
    rel_simple(res[k + j], ms[j])
}

/// The spec's step at a position, opaque so that the proofs about runs do not unfold it.
#[verifier::opaque]
pub open spec fn sub_step(v: Seq<ComponentValue>, i: int, hi: int) -> Step<Simple> {
    subclass_selector(v, i, hi)
}

/// The spec's run of subclass selectors, one step unfolded, in terms of [`sub_step`].
pub proof fn lemma_subs_unfold(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool)
    ensures
        subclass_selectors(v, i, hi, acc, np) == match sub_step(v, i, hi) {
            Step::Invalid => None,
            Step::Found { value, next } => if i < next && next <= hi {
                subclass_selectors(v, next, hi, acc.push(value), np)
            } else {
                None
            },
            Step::Absent => pseudo_compound(v, i, hi, acc, np),
        },
{
    reveal_with_fuel(subclass_selectors, 2);
    reveal(sub_step);
}

/// A step that finds a selector is at something the transcription's run does not stop at.
pub proof fn lemma_sub_step_pre(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p < end <= v.len(),
    ensures
        match sub_step(v, p, end) {
            Step::Found { .. } => !i_is_ws(v[p]) && i_comb_of(v[p]) is None,
            _ => true,
        },
{
    reveal(sub_step);
    lemma_sub_one_pre(v, p, end);
}

/// The transcription reads what the spec's step finds, where it has a counterpart.
pub proof fn lemma_sub_step_a(v: Seq<ComponentValue>, p: int, end: int, in_has: bool, m: ISimple)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
    ensures
        match sub_step(v, p, end) {
            Step::Found { value, next } => rel_simple(value, m) ==> i_sub_one(
                v,
                p,
                end,
                cx0(),
                in_has,
            ) == Some((m, next)),
            _ => true,
        },
{
    reveal(sub_step);
    lemma_sub_one_a(v, p, end, in_has, m);
}

/// Nothing is found at the end.
pub proof fn lemma_sub_step_end(v: Seq<ComponentValue>, p: int, end: int)
    requires
        p >= end,
        end <= v.len(),
    ensures
        sub_step(v, p, end) is Absent,
{
    reveal(sub_step);
}

/// The spec's run of subclass selectors that ends at a boundary, and has a transcription, is
/// read the same by the transcription.
pub proof fn lemma_subs_a(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Simple>,
    np: bool,
    fuel: nat,
    res: Seq<Simple>,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        fuel >= end - p + 1,
        subclass_selectors(v, p, end, acc, np) == Some((res, q)),
        res.len() == acc.len() + ms.len(),
        forall|j: int| 0 <= j < ms.len() ==> #[trigger] relx(res, acc.len() as int, ms, j),
        boundary(v, q, end),
    ensures
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((ms, q)),
    decreases end - p,
{
    lemma_subs_unfold(v, p, end, acc, np);
    let k = acc.len() as int;
    if p >= end {
        lemma_sub_step_end(v, p, end);
        lemma_pseudo_compound(v, p, end, acc, np);
        lemma_colon_at(v, p, end);
        assert(pseudo_element(v, p, end) is Absent);
        assert(ms.len() == 0);
        assert(ms =~= Seq::<ISimple>::empty());
        assert(q == p);
        lemma_i_subs_stop(v, p, end, in_has, fuel);
    } else {
        lemma_sub_step_pre(v, p, end);
        match sub_step(v, p, end) {
            Step::Found { value, next } => {
                assert(p < next && next <= end);
                let acc2 = acc.push(value);
                lemma_subs_prefix(v, next, end, acc2, np);
                assert(res.subrange(0, acc2.len() as int) == acc2);
                assert(acc2[k] == value);
                assert(res.subrange(0, acc2.len() as int)[k] == res[k]);
                assert(res[k] == value);
                assert(ms.len() > 0);
                assert(relx(res, k, ms, 0));
                reveal(relx);
                assert(rel_simple(value, ms[0]));
                lemma_sub_step_a(v, p, end, in_has, ms[0]);
                let ms1 = ms.drop_first();
                assert forall|j: int| 0 <= j < ms1.len() implies #[trigger] relx(res, acc2.len() as int, ms1, j) by {
                    assert(ms1[j] == ms[j + 1]);
                    assert(relx(res, k, ms, j + 1));
                    assert(res[k + (j + 1)] == res[acc2.len() + j]);
                }
                lemma_subs_a(v, next, end, acc2, np, (fuel - 1) as nat, res, ms1, q, in_has);
                lemma_i_subs_step(v, p, end, in_has, fuel, ms[0], next, ms1, q);
                assert(ms =~= seq![ms[0]] + ms1);
            },
            Step::Invalid => {},
            Step::Absent => {
                lemma_pseudo_compound(v, p, end, acc, np);
                assert(res.len() == acc.len()) by {
                    if res.len() > acc.len() {
                        assert(relx(res, k, ms, 0));
                        reveal(relx);
                        assert(rel_simple(res[k + 0], ms[0]));
                    }
                }
                assert(q == p);
                assert(ms =~= Seq::<ISimple>::empty());
                lemma_colon_at(v, p, end);
                lemma_i_subs_stop(v, p, end, in_has, fuel);
            },
        }
    }
}


/// What the transcription's subclass selector reads is what the spec's step finds.
pub proof fn lemma_sub_step_b(v: Seq<ComponentValue>, p: int, end: int, in_has: bool)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
    ensures
        match i_sub_one(v, p, end, cx0(), in_has) {
            Some((m, q)) => match sub_step(v, p, end) {
                Step::Found { value, next } => next == q && sok(value),
                _ => false,
            },
            None => true,
        },
{
    reveal(sub_step);
    lemma_sub_one_b(v, p, end, in_has);
}

/// The spec's step is absent where the transcription's run stops.
pub proof fn lemma_sub_step_stop(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p < end <= v.len(),
        i_is_ws(v[p]) || i_comb_of(v[p]) is Some,
    ensures
        sub_step(v, p, end) is Absent,
{
    reveal(sub_step);
}

/// Where the spec's step is absent and the position is a boundary, nothing more is added.
pub proof fn lemma_pseudo_compound_boundary(v: Seq<ComponentValue>, p: int, end: int, acc: Seq<Simple>, np: bool)
    requires
        0 <= p <= end <= v.len(),
        boundary(v, p, end),
    ensures
        pseudo_compound(v, p, end, acc, np) == Some((acc, p)),
{
    lemma_colon_at(v, p, end);
}

/// What the transcription reads as a run of subclass selectors, the spec reads too.
pub proof fn lemma_subs_b(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Simple>,
    np: bool,
    fuel: nat,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((ms, q)),
    ensures
        boundary(v, q, end),
        p <= q <= end,
        ms.len() > 0 ==> p < q,
        match subclass_selectors(v, p, end, acc, np) {
            Some((res, q2)) => q2 == q && res.len() == acc.len() + ms.len() && forall|j: int|
                0 <= j < ms.len() ==> sok(#[trigger] res[acc.len() + j]),
            None => false,
        },
    decreases fuel,
{
    reveal_with_fuel(i_subs, 2);
    lemma_subs_unfold(v, p, end, acc, np);
    if p >= end || i_is_ws(v[p]) || i_comb_of(v[p]) is Some {
        if p >= end {
            lemma_sub_step_end(v, p, end);
        } else {
            lemma_sub_step_stop(v, p, end);
        }
        assert(boundary(v, p, end));
        lemma_pseudo_compound_boundary(v, p, end, acc, np);
        assert(ms =~= Seq::<ISimple>::empty());
    } else {
        lemma_sub_one_pos(v, p, end, in_has);
        lemma_sub_step_b(v, p, end, in_has);
        match i_sub_one(v, p, end, cx0(), in_has) {
            Some((m, next)) => {
                match i_subs(v, next, end, cx0(), in_has, (fuel - 1) as nat) {
                    Some((ms1, q1)) => {
                        match sub_step(v, p, end) {
                            Step::Found { value, next: next2 } => {
                                assert(next2 == next);
                                lemma_subs_b(v, next, end, acc.push(value), np, (fuel - 1) as nat, ms1, q1, in_has);
                                assert(ms =~= seq![m] + ms1);
                                if let Some((res, q2)) = subclass_selectors(v, p, end, acc, np) {
                                    let acc2 = acc.push(value);
                                    lemma_subs_prefix(v, next, end, acc2, np);
                                    assert(res.subrange(0, acc2.len() as int) == acc2);
                                    assert(res.subrange(0, acc2.len() as int)[acc.len() as int] == res[acc.len() as int]);
                                    assert(res[acc.len() as int] == value);
                                    assert forall|j: int| 0 <= j < ms.len() implies sok(#[trigger] res[acc.len() + j]) by {
                                        if j == 0 {
                                            assert(sok(res[acc.len() as int]));
                                        } else {
                                            assert(ms1[j - 1] == ms[j]);
                                            assert(res[acc2.len() as int + (j - 1)] == res[acc.len() as int + j]);
                                        }
                                    }
                                }
                            },
                            _ => {},
                        }
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}


// ------------------------------------------------------------------------------------
// Compound selectors
// ------------------------------------------------------------------------------------

/// What the spec's steps add to a compound selector is never a type or universal selector.
pub proof fn lemma_user_actions_not_type(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>)
    ensures
        match user_actions(v, i, hi, acc) {
            Some((r, _)) => forall|k: int| acc.len() <= k < r.len() ==> !is_type_or_universal(#[trigger] r[k]),
            None => true,
        },
    decreases hi - i,
{
    match user_action(v, i, hi) {
        Step::Found { value, next } => {
            if next > i && next <= hi {
                let acc1 = acc.push(Simple::PseudoClass { class: value });
                lemma_user_actions_not_type(v, next, hi, acc1);
                lemma_user_actions_prefix(v, next, hi, acc1);
                if let Some((r, _)) = user_actions(v, next, hi, acc1) {
                    assert forall|k: int| acc.len() <= k < r.len() implies !is_type_or_universal(#[trigger] r[k]) by {
                        if k == acc.len() {
                            assert(r.subrange(0, acc1.len() as int)[k] == acc1[k]);
                        }
                    }
                }
            }
        },
        _ => {},
    }
}

/// The spec's step finds no type or universal selector.
pub proof fn lemma_sub_step_not_type(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p < end <= v.len(),
    ensures
        match sub_step(v, p, end) {
            Step::Found { value, .. } => !is_type_or_universal(value),
            _ => true,
        },
{
    reveal(sub_step);
}

/// A run of subclass selectors adds no type or universal selector.
pub proof fn lemma_subs_not_type(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool)
    requires
        0 <= i <= hi <= v.len(),
    ensures
        match subclass_selectors(v, i, hi, acc, np) {
            Some((r, _)) => forall|k: int| acc.len() <= k < r.len() ==> !is_type_or_universal(#[trigger] r[k]),
            None => true,
        },
    decreases hi - i,
{
    lemma_subs_unfold(v, i, hi, acc, np);
    if i < hi {
        lemma_sub_step_not_type(v, i, hi);
    }
    match sub_step(v, i, hi) {
        Step::Found { value, next } => {
            if i < next && next <= hi {
                let acc2 = acc.push(value);
                lemma_subs_not_type(v, next, hi, acc2, np);
                lemma_subs_prefix(v, next, hi, acc2, np);
                if let Some((r, _)) = subclass_selectors(v, next, hi, acc2, np) {
                    assert forall|k: int| acc.len() <= k < r.len() implies !is_type_or_universal(#[trigger] r[k]) by {
                        if k == acc.len() {
                            assert(r.subrange(0, acc2.len() as int)[k] == acc2[k]);
                        }
                    }
                }
            }
        },
        Step::Absent => {
            lemma_pseudo_compound_not_type(v, i, hi, acc, np);
        },
        _ => {},
    }
}

/// What the spec's `<pseudo-compound-selector>` adds is never a type or universal selector.
pub proof fn lemma_pseudo_compound_not_type(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool)
    ensures
        match pseudo_compound(v, i, hi, acc, np) {
            Some((r, _)) => forall|k: int| acc.len() <= k < r.len() ==> !is_type_or_universal(#[trigger] r[k]),
            None => true,
        },
{
    match pseudo_element(v, i, hi) {
        Step::Found { value, next } => {
            if !np {
                let acc1 = acc.push(Simple::PseudoElement { element: value });
                lemma_user_actions_not_type(v, next, hi, acc1);
                lemma_user_actions_prefix(v, next, hi, acc1);
                if let Some((r, _)) = user_actions(v, next, hi, acc1) {
                    assert forall|k: int| acc.len() <= k < r.len() implies !is_type_or_universal(#[trigger] r[k]) by {
                        if k == acc.len() {
                            assert(r.subrange(0, acc1.len() as int)[k] == acc1[k]);
                        }
                    }
                }
            }
        },
        _ => {},
    }
}


/// Where the spec's type selector ends, and what it is.
pub proof fn lemma_type_selector_pos(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p,
        end <= v.len(),
    ensures
        match type_selector(v, p, end) {
            Step::Found { value, next } => p < next <= end && is_type_or_universal(value),
            _ => true,
        },
{
    lemma_ident_at(v, p, end);
    lemma_ident_at(v, p + 1, end);
    lemma_ident_at(v, p + 2, end);
    lemma_delim_at(v, p, end, 0x2A);
    lemma_delim_at(v, p + 1, end, 0x7C);
    lemma_delim_at(v, p + 2, end, 0x2A);
    lemma_delim_at(v, p, end, 0x7C);
}

/// A transcription's type selector is the one for a spec's, given they are related.
pub proof fn lemma_rel_type_unique(s: Simple, t1: IType, t2: IType)
    requires
        rel_type(s, t1),
        rel_type(s, t2),
    ensures
        t1 == t2,
{
}

/// The spec's run of subclass selectors, opaque for the proofs about compound selectors.
#[verifier::opaque]
pub open spec fn subs_res(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, np: bool) -> Option<
    (Seq<Simple>, int),
> {
    subclass_selectors(v, i, hi, acc, np)
}

/// The spec's compound selector, opaque for the proofs about complex selectors.
#[verifier::opaque]
pub open spec fn comp_res(v: Seq<ComponentValue>, i: int, hi: int, np: bool) -> Option<(Seq<Simple>, int)> {
    compound_selector(v, i, hi, np)
}

/// The spec's compound selector, one step unfolded, in terms of [`subs_res`].
pub proof fn lemma_comp_unfold(v: Seq<ComponentValue>, i: int, hi: int, np: bool)
    ensures
        comp_res(v, i, hi, np) == match type_selector(v, i, hi) {
            Step::Invalid => None,
            Step::Absent => subs_res(v, i, hi, Seq::empty(), np),
            Step::Found { value, next } => if i < next && next <= hi {
                subs_res(v, next, hi, seq![value], np)
            } else {
                None
            },
        },
{
    reveal(comp_res);
    reveal(subs_res);
}

/// [`lemma_subs_a`], in terms of [`subs_res`].
pub proof fn lemma_subs_a_res(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Simple>,
    np: bool,
    fuel: nat,
    res: Seq<Simple>,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        fuel >= end - p + 1,
        subs_res(v, p, end, acc, np) == Some((res, q)),
        res.len() == acc.len() + ms.len(),
        forall|j: int| 0 <= j < ms.len() ==> #[trigger] relx(res, acc.len() as int, ms, j),
        boundary(v, q, end),
    ensures
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((ms, q)),
{
    reveal(subs_res);
    lemma_subs_a(v, p, end, acc, np, fuel, res, ms, q, in_has);
}

/// [`lemma_subs_b`], in terms of [`subs_res`].
pub proof fn lemma_subs_b_res(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Simple>,
    np: bool,
    fuel: nat,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        i_subs(v, p, end, cx0(), in_has, fuel) == Some((ms, q)),
    ensures
        boundary(v, q, end),
        p <= q <= end,
        ms.len() > 0 ==> p < q,
        match subs_res(v, p, end, acc, np) {
            Some((res, q2)) => q2 == q && res.len() == acc.len() + ms.len() && forall|j: int|
                0 <= j < ms.len() ==> sok(#[trigger] res[acc.len() + j]),
            None => false,
        },
{
    reveal(subs_res);
    lemma_subs_b(v, p, end, acc, np, fuel, ms, q, in_has);
}

/// [`lemma_subs_prefix`] and [`lemma_subs_not_type`], in terms of [`subs_res`].
pub proof fn lemma_subs_facts_res(v: Seq<ComponentValue>, p: int, end: int, acc: Seq<Simple>, np: bool)
    requires
        0 <= p <= end <= v.len(),
    ensures
        match subs_res(v, p, end, acc, np) {
            Some((r, _)) => r.len() >= acc.len() && r.subrange(0, acc.len() as int) == acc && forall|k: int|
                acc.len() <= k < r.len() ==> !is_type_or_universal(#[trigger] r[k]),
            None => true,
        },
{
    reveal(subs_res);
    lemma_subs_prefix(v, p, end, acc, np);
    lemma_subs_not_type(v, p, end, acc, np);
}

/// A compound selector the spec reads, that ends at a boundary and has a transcription, the
/// transcription reads.
pub proof fn lemma_compound_a(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    res: Seq<Simple>,
    mc: ICompound,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        comp_res(v, p, end, np) == Some((res, q)),
        rel_compound(res, mc),
        boundary(v, q, end),
    ensures
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
{
    lemma_comp_unfold(v, p, end, np);
    lemma_type_selector(v, p, end);
    lemma_type_selector_pos(v, p, end);
    match type_selector(v, p, end) {
        Step::Found { value, next } => {
            let acc = seq![value];
            assert(p < next <= end);
            lemma_subs_facts_res(v, next, end, acc, np);
            assert(res.subrange(0, 1) == acc);
            assert(res.subrange(0, 1)[0] == res[0]);
            assert(acc[0] == value);
            assert(res[0] == value);
            assert(comp_off(res) == 1);
            match i_type_selector(v, p, end, cx0()) {
                Some(Some((t, q1))) => {
                    assert(q1 == next && rel_type(value, t));
                    match mc.ty {
                        Some(t2) => {
                            assert(rel_type(res[0], t2));
                            lemma_rel_type_unique(value, t, t2);
                        },
                        None => {},
                    }
                    assert forall|j: int| 0 <= j < mc.subs.len() implies #[trigger] relx(res, 1, mc.subs, j) by {
                        reveal(relx);
                        assert(rel_simple(res[comp_off(res) + j], mc.subs[j]));
                    }
                    lemma_subs_a_res(v, next, end, acc, np, i_fuel(next, end), res, mc.subs, q, in_has);
                    assert(mc == (ICompound { ty: Some(t), subs: mc.subs }));
                },
                _ => {},
            }
        },
        Step::Absent => {
            let acc = Seq::<Simple>::empty();
            lemma_subs_facts_res(v, p, end, acc, np);
            assert(res.len() > 0);
            assert(comp_off(res) == 0);
            assert forall|j: int| 0 <= j < mc.subs.len() implies #[trigger] relx(res, 0, mc.subs, j) by {
                reveal(relx);
                assert(rel_simple(res[comp_off(res) + j], mc.subs[j]));
            }
            lemma_subs_a_res(v, p, end, acc, np, i_fuel(p, end), res, mc.subs, q, in_has);
            assert(mc.ty is None);
            assert(mc == (ICompound { ty: None, subs: mc.subs }));
        },
        Step::Invalid => {},
    }
}

/// A compound selector that begins with a type selector, as the transcription reads it.
pub proof fn lemma_compound_b_found(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    value: Simple,
    next: int,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p < next <= end <= v.len(),
        no_fun(v, end),
        type_selector(v, p, end) == (Step::Found { value, next }),
        i_subs(v, next, end, cx0(), in_has, i_fuel(next, end)) == Some((ms, q)),
    ensures
        boundary(v, q, end),
        p < q <= end,
        match comp_res(v, p, end, np) {
            Some((res, q2)) => q2 == q && res.len() == 1 + ms.len() && res[0] == value && forall|j: int|
                0 <= j < ms.len() ==> sok(#[trigger] res[1 + j]),
            None => false,
        },
{
    lemma_comp_unfold(v, p, end, np);
    lemma_subs_b_res(v, next, end, seq![value], np, i_fuel(next, end), ms, q, in_has);
    lemma_subs_facts_res(v, next, end, seq![value], np);
    if let Some((res, _)) = subs_res(v, next, end, seq![value], np) {
        assert(res.subrange(0, 1) == seq![value]);
        assert(res.subrange(0, 1)[0] == res[0]);
    }
}

/// A compound selector that does not begin with a type selector, as the transcription reads it.
pub proof fn lemma_compound_b_absent(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    ms: Seq<ISimple>,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        type_selector(v, p, end) is Absent,
        ms.len() > 0,
        i_subs(v, p, end, cx0(), in_has, i_fuel(p, end)) == Some((ms, q)),
    ensures
        boundary(v, q, end),
        p < q <= end,
        match comp_res(v, p, end, np) {
            Some((res, q2)) => q2 == q && res.len() == ms.len() && forall|j: int|
                0 <= j < ms.len() ==> sok(#[trigger] res[0 + j]),
            None => false,
        },
{
    lemma_comp_unfold(v, p, end, np);
    lemma_subs_b_res(v, p, end, Seq::<Simple>::empty(), np, i_fuel(p, end), ms, q, in_has);
}

/// A compound selector the transcription reads, the spec reads too, to the same place, and what
/// it read has no pseudo-element.
pub proof fn lemma_compound_b(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    mc: ICompound,
    q: int,
    in_has: bool,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
    ensures
        p < q <= end,
        boundary(v, q, end),
        match comp_res(v, p, end, np) {
            Some((res, q2)) => q2 == q && res.len() > 0 && forall|k: int|
                0 <= k < res.len() ==> !(#[trigger] res[k] is PseudoElement),
            None => false,
        },
{
    lemma_type_selector(v, p, end);
    lemma_type_selector_pos(v, p, end);
    match i_type_selector(v, p, end, cx0()) {
        Some(Some((t, q1))) => {
            match i_subs(v, q1, end, cx0(), in_has, i_fuel(q1, end)) {
                Some((ms, q3)) => {
                    match type_selector(v, p, end) {
                        Step::Found { value, next } => {
                            lemma_compound_b_found(v, p, end, np, value, next, ms, q3, in_has);
                            if let Some((res, q2)) = comp_res(v, p, end, np) {
                                assert forall|k: int| 0 <= k < res.len() implies !(#[trigger] res[k] is PseudoElement) by {
                                    if k >= 1 {
                                        assert(sok(res[1 + (k - 1)]));
                                    }
                                }
                            }
                        },
                        _ => {},
                    }
                },
                None => {},
            }
        },
        Some(None) => {
            match i_subs(v, p, end, cx0(), in_has, i_fuel(p, end)) {
                Some((ms, q3)) => {
                    assert(ms.len() > 0);
                    lemma_compound_b_absent(v, p, end, np, ms, q3, in_has);
                    if let Some((res, q2)) = comp_res(v, p, end, np) {
                        assert forall|k: int| 0 <= k < res.len() implies !(#[trigger] res[k] is PseudoElement) by {
                            assert(sok(res[0 + k]));
                        }
                    }
                },
                None => {},
            }
        },
        None => {},
    }
}

/// No pseudo-element among the simple selectors of a compound selector.
pub proof fn lemma_no_pe(c: Seq<Simple>, k: int)
    requires
        0 <= k <= c.len(),
        forall|j: int| 0 <= j < c.len() ==> !(#[trigger] c[j] is PseudoElement),
    ensures
        !pseudo_element_within(c, k),
    decreases k,
{
    if k > 0 {
        lemma_no_pe(c, k - 1);
    }
}

// ------------------------------------------------------------------------------------
// Complex selectors
// ------------------------------------------------------------------------------------

/// The spec's loop over the units of a complex selector, opaque for the proofs about it.
#[verifier::opaque]
pub open spec fn cloop_res(
    v: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    bs: Seq<Combinator>,
    np: bool,
) -> Option<Complex> {
    complex_selector_loop(v, i, hi, cs, bs, np)
}

/// The spec's loop, one step unfolded, in terms of [`comp_res`].
pub proof fn lemma_cloop_unfold(
    v: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    bs: Seq<Combinator>,
    np: bool,
)
    ensures
        cloop_res(v, i, hi, cs, bs, np) == match comp_res(v, i, hi, np) {
            None => None,
            Some((compound, next)) => if next <= i || next > hi {
                None
            } else {
                let cs2 = cs.push(compound);
                let after = skip_whitespace(v, next, hi);
                if after >= hi {
                    Some(Complex { compounds: cs2, combinators: bs })
                } else if has_pseudo_element(compound) {
                    None
                } else {
                    match combinator_at(v, after, hi) {
                        Some(c) => {
                            let start = skip_whitespace(v, after + 1, hi);
                            if start >= hi {
                                None
                            } else {
                                cloop_res(v, start, hi, cs2, bs.push(c), np)
                            }
                        },
                        None => if after > next {
                            cloop_res(v, after, hi, cs2, bs.push(Combinator::Descendant), np)
                        } else {
                            None
                        },
                    }
                }
            },
        },
{
    reveal_with_fuel(complex_selector_loop, 2);
    reveal(cloop_res);
    reveal(comp_res);
}

/// The loop's result extends what was read before.
pub proof fn lemma_cloop_prefix(
    v: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    bs: Seq<Combinator>,
    np: bool,
)
    requires
        0 <= i,
        hi <= v.len(),
    ensures
        match cloop_res(v, i, hi, cs, bs, np) {
            Some(c) => c.compounds.len() >= cs.len() && c.compounds.subrange(0, cs.len() as int) == cs
                && c.combinators.len() >= bs.len() && c.combinators.subrange(0, bs.len() as int) == bs,
            None => true,
        },
    decreases hi - i,
{
    lemma_cloop_unfold(v, i, hi, cs, bs, np);
    if let Some((compound, next)) = comp_res(v, i, hi, np) {
        if !(next <= i || next > hi) {
            let cs2 = cs.push(compound);
            lemma_skip_same(v, next, hi);
            let after = skip_whitespace(v, next, hi);
            if after < hi && !has_pseudo_element(compound) {
                lemma_combinator_at(v, after, hi);
                match combinator_at(v, after, hi) {
                    Some(c) => {
                        lemma_skip_same(v, after + 1, hi);
                        let start = skip_whitespace(v, after + 1, hi);
                        if start < hi {
                            let bs2 = bs.push(c);
                            lemma_cloop_prefix(v, start, hi, cs2, bs2, np);
                            if let Some(r) = cloop_res(v, start, hi, cs2, bs2, np) {
                                assert(r.compounds.subrange(0, cs.len() as int) =~= cs);
                                assert(r.combinators.subrange(0, bs.len() as int) =~= bs);
                            }
                        }
                    },
                    None => {
                        if after > next {
                            let bs2 = bs.push(Combinator::Descendant);
                            lemma_cloop_prefix(v, after, hi, cs2, bs2, np);
                            if let Some(r) = cloop_res(v, after, hi, cs2, bs2, np) {
                                assert(r.compounds.subrange(0, cs.len() as int) =~= cs);
                                assert(r.combinators.subrange(0, bs.len() as int) =~= bs);
                            }
                        }
                    },
                }
            }
        }
    }
}


/// The `j`-th transcribed compound selector is the counterpart of the `k + j`-th spec one.
#[verifier::opaque]
pub open spec fn relc(cs: Seq<Seq<Simple>>, k: int, ms: Seq<ICompound>, j: int) -> bool {
    rel_compound(cs[k + j], ms[j])
}

/// The `j`-th transcribed combinator is the counterpart of the `k + j`-th spec one.
#[verifier::opaque]
pub open spec fn relb(bs: Seq<Combinator>, k: int, ms: Seq<IComb>, j: int) -> bool {
    rel_comb(bs[k + j], ms[j])
}

/// A compound selector with a transcription has no pseudo-element.
pub proof fn lemma_rel_no_pseudo(c: Seq<Simple>, m: ICompound, k: int)
    requires
        rel_compound(c, m),
        0 <= k <= c.len(),
    ensures
        !pseudo_element_within(c, k),
    decreases k,
{
    if k > 0 {
        lemma_rel_no_pseudo(c, m, k - 1);
        let off = comp_off(c);
        if k - 1 >= off {
            assert(rel_simple(c[off + (k - 1 - off)], m.subs[k - 1 - off]));
        } else {
            assert(is_type_or_universal(c[0]));
        }
    }
}

/// The transcription's loop over units, when the first compound selector is the only one.
pub proof fn lemma_i_units_one(v: Seq<ComponentValue>, p: int, end: int, in_has: bool, fuel: nat, mc: ICompound, q: int)
    requires
        0 <= p < end <= v.len(),
        fuel > 0,
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q >= end || i_skip_ws(v, q, end) >= end,
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((seq![mc], Seq::<IComb>::empty())),
{
    reveal_with_fuel(i_units, 2);
}

/// The transcription's loop over units, after a combinator.
pub proof fn lemma_i_units_comb(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    in_has: bool,
    fuel: nat,
    mc: ICompound,
    q: int,
    r: int,
    comb: IComb,
    r2: int,
    mus1: Seq<ICompound>,
    mbs1: Seq<IComb>,
)
    requires
        0 <= p < end <= v.len(),
        fuel > 0,
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q < end,
        r == i_skip_ws(v, q, end),
        r < end,
        i_comb_of(v[r]) == Some(comb),
        r2 == i_skip_ws(v, r + 1, end),
        r2 < end,
        i_units(v, r2, end, cx0(), in_has, (fuel - 1) as nat) == Some((mus1, mbs1)),
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((seq![mc] + mus1, seq![comb] + mbs1)),
{
    reveal_with_fuel(i_units, 2);
}

/// The transcription's loop over units, after white space alone.
pub proof fn lemma_i_units_desc(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    in_has: bool,
    fuel: nat,
    mc: ICompound,
    q: int,
    r: int,
    mus1: Seq<ICompound>,
    mbs1: Seq<IComb>,
)
    requires
        0 <= p < end <= v.len(),
        fuel > 0,
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q < end,
        r == i_skip_ws(v, q, end),
        r < end,
        i_comb_of(v[r]) is None,
        r > q,
        i_units(v, r, end, cx0(), in_has, (fuel - 1) as nat) == Some((mus1, mbs1)),
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((seq![mc] + mus1, seq![IComb::Descendant] + mbs1)),
{
    reveal_with_fuel(i_units, 2);
}


/// A combinator's counterpart is determined.
pub proof fn lemma_rel_comb_unique(c: Combinator, m1: IComb, m2: IComb)
    requires
        rel_comb(c, m1),
        rel_comb(c, m2),
    ensures
        m1 == m2,
{
}

/// The first compound selector of the spec's loop, and what follows it.
pub proof fn lemma_units_first(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cs0: Seq<Seq<Simple>>,
    bs0: Seq<Combinator>,
    np: bool,
    c: Complex,
    mus: Seq<ICompound>,
    in_has: bool,
)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
        cloop_res(v, p, end, cs0, bs0, np) == Some(c),
        c.compounds.len() == cs0.len() + mus.len(),
        mus.len() >= 1,
        forall|j: int| 0 <= j < mus.len() ==> #[trigger] relc(c.compounds, cs0.len() as int, mus, j),
    ensures
        match comp_res(v, p, end, np) {
            Some((compound, next)) => {
                &&& p < next <= end
                &&& c.compounds.len() > cs0.len()
                &&& c.compounds[cs0.len() as int] == compound
                &&& rel_compound(compound, mus[0])
                &&& i_compound(v, p, end, cx0(), in_has) == Some((mus[0], next))
                &&& !has_pseudo_element(compound)
            },
            None => false,
        },
{
    lemma_cloop_unfold(v, p, end, cs0, bs0, np);
    lemma_cloop_prefix(v, p, end, cs0, bs0, np);
    let k = cs0.len() as int;
    if let Some((compound, next)) = comp_res(v, p, end, np) {
        if p < next <= end {
            lemma_skip_same(v, next, end);
            let after = skip_whitespace(v, next, end);
            let cs2 = cs0.push(compound);
            if after >= end {
                // `c` is the loop's last step.
            } else {
                lemma_combinator_at(v, after, end);
                match combinator_at(v, after, end) {
                    Some(cb) => {
                        lemma_skip_same(v, after + 1, end);
                        let start = skip_whitespace(v, after + 1, end);
                        if start < end {
                            lemma_cloop_prefix(v, start, end, cs2, bs0.push(cb), np);
                        }
                    },
                    None => {
                        lemma_cloop_prefix(v, after, end, cs2, bs0.push(Combinator::Descendant), np);
                    },
                }
            }
            assert(c.compounds.subrange(0, cs2.len() as int) == cs2);
            assert(c.compounds.subrange(0, cs2.len() as int)[k] == c.compounds[k]);
            assert(cs2[k] == compound);
            assert(relc(c.compounds, k, mus, 0));
            reveal(relc);
            assert(rel_compound(compound, mus[0]));
            lemma_rel_no_pseudo(compound, mus[0], compound.len() as int);
            // The compound selector ends at a boundary.
            assert(boundary(v, next, end)) by {
                if after < end {
                    match combinator_at(v, after, end) {
                        Some(cb) => {
                            assert(next == after || next < after);
                        },
                        None => {},
                    }
                }
            }
            lemma_compound_a(v, p, end, np, compound, mus[0], next, in_has);
        }
    }
}

/// [`relc`] one item along.
pub proof fn lemma_relc_shift(cs: Seq<Seq<Simple>>, k: int, mus: Seq<ICompound>, j: int)
    requires
        0 <= j,
        j + 1 < mus.len(),
    ensures
        relc(cs, k + 1, mus.drop_first(), j) == relc(cs, k, mus, j + 1),
{
    reveal(relc);
    assert(mus.drop_first()[j] == mus[j + 1]);
}

/// [`relb`] one item along.
pub proof fn lemma_relb_shift(bs: Seq<Combinator>, k: int, mbs: Seq<IComb>, j: int)
    requires
        0 <= j,
        j + 1 < mbs.len(),
    ensures
        relb(bs, k + 1, mbs.drop_first(), j) == relb(bs, k, mbs, j + 1),
{
    reveal(relb);
    assert(mbs.drop_first()[j] == mbs[j + 1]);
}

/// The head of a [`relc`].
pub proof fn lemma_relc_head(cs: Seq<Seq<Simple>>, k: int, mus: Seq<ICompound>)
    requires
        mus.len() >= 1,
        relc(cs, k, mus, 0),
    ensures
        rel_compound(cs[k], mus[0]),
{
    reveal(relc);
}

/// The head of a [`relb`].
pub proof fn lemma_relb_head(bs: Seq<Combinator>, k: int, mbs: Seq<IComb>)
    requires
        mbs.len() >= 1,
        relb(bs, k, mbs, 0),
    ensures
        rel_comb(bs[k], mbs[0]),
{
    reveal(relb);
}

/// The spec's loop over units, with the combinator after the first compound selector, and the
/// rest of the loop read by the transcription.
pub proof fn lemma_units_a_comb(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    in_has: bool,
    next: int,
    after: int,
    start: int,
    cb: Combinator,
    mus1: Seq<ICompound>,
    mbs1: Seq<IComb>,
)
    requires
        0 <= p < next <= end <= v.len(),
        fuel > 0,
        mus.len() >= 1,
        mbs.len() >= 1,
        mus1 == mus.drop_first(),
        mbs1 == mbs.drop_first(),
        i_compound(v, p, end, cx0(), in_has) == Some((mus[0], next)),
        after == i_skip_ws(v, next, end),
        after < end,
        combinator_at(v, after, end) == Some(cb),
        start == i_skip_ws(v, after + 1, end),
        start < end,
        rel_comb(cb, mbs[0]),
        i_units(v, start, end, cx0(), in_has, (fuel - 1) as nat) == Some((mus1, mbs1)),
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
{
    lemma_combinator_at(v, after, end);
    let comb = i_comb_of(v[after]).unwrap();
    lemma_rel_comb_unique(cb, comb, mbs[0]);
    lemma_i_units_comb(v, p, end, in_has, fuel, mus[0], next, after, comb, start, mus1, mbs1);
    assert(mus =~= seq![mus[0]] + mus1);
    assert(mbs =~= seq![comb] + mbs1);
}

/// The same after white space alone.
pub proof fn lemma_units_a_desc(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    np: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    in_has: bool,
    next: int,
    after: int,
    mus1: Seq<ICompound>,
    mbs1: Seq<IComb>,
)
    requires
        0 <= p < next <= end <= v.len(),
        fuel > 0,
        mus.len() >= 1,
        mbs.len() >= 1,
        mus1 == mus.drop_first(),
        mbs1 == mbs.drop_first(),
        i_compound(v, p, end, cx0(), in_has) == Some((mus[0], next)),
        after == i_skip_ws(v, next, end),
        after < end,
        after > next,
        combinator_at(v, after, end) is None,
        rel_comb(Combinator::Descendant, mbs[0]),
        i_units(v, after, end, cx0(), in_has, (fuel - 1) as nat) == Some((mus1, mbs1)),
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
{
    lemma_combinator_at(v, after, end);
    lemma_i_units_desc(v, p, end, in_has, fuel, mus[0], next, after, mus1, mbs1);
    assert(mus =~= seq![mus[0]] + mus1);
    assert(mbs =~= seq![IComb::Descendant] + mbs1);
}

/// The spec's loop over units that has a transcription is read the same by the transcription.
#[verifier::rlimit(40)]
pub proof fn lemma_units_a(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cs0: Seq<Seq<Simple>>,
    bs0: Seq<Combinator>,
    np: bool,
    fuel: nat,
    c: Complex,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    in_has: bool,
)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
        fuel >= end - p + 1,
        cloop_res(v, p, end, cs0, bs0, np) == Some(c),
        c.compounds.len() == cs0.len() + mus.len(),
        c.combinators.len() == bs0.len() + mbs.len(),
        mus.len() >= 1,
        mbs.len() + 1 == mus.len(),
        forall|j: int| 0 <= j < mus.len() ==> #[trigger] relc(c.compounds, cs0.len() as int, mus, j),
        forall|j: int| 0 <= j < mbs.len() ==> #[trigger] relb(c.combinators, bs0.len() as int, mbs, j),
    ensures
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
    decreases end - p,
{
    lemma_units_first(v, p, end, cs0, bs0, np, c, mus, in_has);
    lemma_cloop_unfold(v, p, end, cs0, bs0, np);
    let k = cs0.len() as int;
    let kb = bs0.len() as int;
    if let Some((compound, next)) = comp_res(v, p, end, np) {
        let cs2 = cs0.push(compound);
        lemma_skip_same(v, next, end);
        let after = skip_whitespace(v, next, end);
        if after >= end {
            assert(c == (Complex { compounds: cs2, combinators: bs0 }));
            assert(mus =~= seq![mus[0]]);
            assert(mbs =~= Seq::<IComb>::empty());
            lemma_skip_ws(v, next, end);
            lemma_i_units_one(v, p, end, in_has, fuel, mus[0], next);
        } else {
            lemma_combinator_at(v, after, end);
            lemma_skip_ws(v, next, end);
            match combinator_at(v, after, end) {
                Some(cb) => {
                    lemma_skip_same(v, after + 1, end);
                    let start = skip_whitespace(v, after + 1, end);
                    lemma_skip_ws(v, after + 1, end);
                    let bs2 = bs0.push(cb);
                    lemma_cloop_prefix(v, start, end, cs2, bs2, np);
                    assert(c.combinators.subrange(0, bs2.len() as int)[kb] == c.combinators[kb]);
                    assert(c.combinators[kb] == cb);
                    lemma_relb_head(c.combinators, kb, mbs);
                    let mus1 = mus.drop_first();
                    let mbs1 = mbs.drop_first();
                    assert forall|j: int| 0 <= j < mus1.len() implies #[trigger] relc(c.compounds, cs2.len() as int, mus1, j) by {
                        lemma_relc_shift(c.compounds, k, mus, j);
                    }
                    assert forall|j: int| 0 <= j < mbs1.len() implies #[trigger] relb(c.combinators, bs2.len() as int, mbs1, j) by {
                        lemma_relb_shift(c.combinators, kb, mbs, j);
                    }
                    lemma_units_a(v, start, end, cs2, bs2, np, (fuel - 1) as nat, c, mus1, mbs1, in_has);
                    lemma_units_a_comb(v, p, end, np, fuel, mus, mbs, in_has, next, after, start, cb, mus1, mbs1);
                },
                None => {
                    let bs2 = bs0.push(Combinator::Descendant);
                    lemma_cloop_prefix(v, after, end, cs2, bs2, np);
                    assert(c.combinators.subrange(0, bs2.len() as int)[kb] == c.combinators[kb]);
                    assert(c.combinators[kb] == Combinator::Descendant);
                    lemma_relb_head(c.combinators, kb, mbs);
                    let mus1 = mus.drop_first();
                    let mbs1 = mbs.drop_first();
                    assert forall|j: int| 0 <= j < mus1.len() implies #[trigger] relc(c.compounds, cs2.len() as int, mus1, j) by {
                        lemma_relc_shift(c.compounds, k, mus, j);
                    }
                    assert forall|j: int| 0 <= j < mbs1.len() implies #[trigger] relb(c.combinators, bs2.len() as int, mbs1, j) by {
                        lemma_relb_shift(c.combinators, kb, mbs, j);
                    }
                    lemma_units_a(v, after, end, cs2, bs2, np, (fuel - 1) as nat, c, mus1, mbs1, in_has);
                    lemma_units_a_desc(v, p, end, np, fuel, mus, mbs, in_has, next, after, mus1, mbs1);
                },
            }
        }
    }
}


/// The transcription's loop over units, when it succeeded with one compound selector.
pub proof fn lemma_i_units_case_one(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    in_has: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    mc: ICompound,
    q: int,
)
    requires
        0 <= p < end <= v.len(),
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q >= end || i_skip_ws(v, q, end) >= end,
    ensures
        mus =~= seq![mc],
        mbs.len() == 0,
        fuel > 0,
{
    reveal_with_fuel(i_units, 2);
}

/// The transcription's loop over units, when it succeeded after a combinator.
pub proof fn lemma_i_units_case_comb(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    in_has: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    mc: ICompound,
    q: int,
    r: int,
)
    requires
        0 <= p < end <= v.len(),
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q < end,
        r == i_skip_ws(v, q, end),
        r < end,
        i_comb_of(v[r]) is Some,
    ensures
        fuel > 0,
        mus.len() >= 1,
        mbs.len() >= 1,
        mus[0] == mc,
        mbs[0] == i_comb_of(v[r]).unwrap(),
        i_skip_ws(v, r + 1, end) < end,
        i_units(v, i_skip_ws(v, r + 1, end), end, cx0(), in_has, (fuel - 1) as nat) == Some(
            (mus.drop_first(), mbs.drop_first()),
        ),
{
    reveal_with_fuel(i_units, 2);
    let r2 = i_skip_ws(v, r + 1, end);
    if r2 < end {
        if let Some((cs, bs)) = i_units(v, r2, end, cx0(), in_has, (fuel - 1) as nat) {
            assert(mus =~= seq![mc] + cs);
            assert(mbs =~= seq![i_comb_of(v[r]).unwrap()] + bs);
            assert(mus.drop_first() =~= cs);
            assert(mbs.drop_first() =~= bs);
        }
    }
}

/// The transcription's loop over units, when it succeeded after white space alone.
pub proof fn lemma_i_units_case_desc(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    in_has: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    mc: ICompound,
    q: int,
    r: int,
)
    requires
        0 <= p < end <= v.len(),
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
        i_compound(v, p, end, cx0(), in_has) == Some((mc, q)),
        q < end,
        r == i_skip_ws(v, q, end),
        r < end,
        i_comb_of(v[r]) is None,
    ensures
        fuel > 0,
        r > q,
        mus.len() >= 1,
        mbs.len() >= 1,
        mus[0] == mc,
        mbs[0] == IComb::Descendant,
        i_units(v, r, end, cx0(), in_has, (fuel - 1) as nat) == Some((mus.drop_first(), mbs.drop_first())),
{
    reveal_with_fuel(i_units, 2);
    if r > q {
        if let Some((cs, bs)) = i_units(v, r, end, cx0(), in_has, (fuel - 1) as nat) {
            assert(mus =~= seq![mc] + cs);
            assert(mbs =~= seq![IComb::Descendant] + bs);
            assert(mus.drop_first() =~= cs);
            assert(mbs.drop_first() =~= bs);
        }
    }
}

/// What the transcription reads as a loop over units, the spec reads too.
#[verifier::rlimit(40)]
pub proof fn lemma_units_b(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cs0: Seq<Seq<Simple>>,
    bs0: Seq<Combinator>,
    np: bool,
    fuel: nat,
    mus: Seq<ICompound>,
    mbs: Seq<IComb>,
    in_has: bool,
)
    requires
        0 <= p < end <= v.len(),
        no_fun(v, end),
        i_units(v, p, end, cx0(), in_has, fuel) == Some((mus, mbs)),
    ensures
        match cloop_res(v, p, end, cs0, bs0, np) {
            Some(c) => c.compounds.len() == cs0.len() + mus.len() && c.combinators.len() == bs0.len()
                + mbs.len(),
            None => false,
        },
    decreases fuel,
{
    lemma_cloop_unfold(v, p, end, cs0, bs0, np);
    reveal_with_fuel(i_units, 2);
    if let Some((mc, q)) = i_compound(v, p, end, cx0(), in_has) {
        lemma_compound_b(v, p, end, np, mc, q, in_has);
        if let Some((res, q2)) = comp_res(v, p, end, np) {
            lemma_no_pe(res, res.len() as int);
            assert(!has_pseudo_element(res));
            let cs2 = cs0.push(res);
            lemma_skip_same(v, q, end);
            let after = skip_whitespace(v, q, end);
            assert(after == i_skip_ws(v, q, end));
            if q >= end || after >= end {
                lemma_i_units_case_one(v, p, end, in_has, fuel, mus, mbs, mc, q);
            } else {
                lemma_skip_ws(v, q, end);
                lemma_combinator_at(v, after, end);
                if i_comb_of(v[after]) is Some {
                    lemma_i_units_case_comb(v, p, end, in_has, fuel, mus, mbs, mc, q, after);
                    let r2 = i_skip_ws(v, after + 1, end);
                    lemma_skip_same(v, after + 1, end);
                    match combinator_at(v, after, end) {
                        Some(cb) => {
                            lemma_units_b(
                                v,
                                r2,
                                end,
                                cs2,
                                bs0.push(cb),
                                np,
                                (fuel - 1) as nat,
                                mus.drop_first(),
                                mbs.drop_first(),
                                in_has,
                            );
                        },
                        None => {},
                    }
                } else {
                    lemma_i_units_case_desc(v, p, end, in_has, fuel, mus, mbs, mc, q, after);
                    lemma_units_b(
                        v,
                        after,
                        end,
                        cs2,
                        bs0.push(Combinator::Descendant),
                        np,
                        (fuel - 1) as nat,
                        mus.drop_first(),
                        mbs.drop_first(),
                        in_has,
                    );
                }
            }
        }
    }
}


/// The transcription's trim keeps what is not white space.
pub proof fn lemma_trim_pos(v: Seq<ComponentValue>, p: int, end: int)
    requires
        0 <= p < end <= v.len(),
        !i_is_ws(v[p]),
    ensures
        p < i_trim_end(v, p, end) <= end,
    decreases end - p,
{
    if p < end && i_is_ws(v[end - 1]) {
        lemma_trim_pos(v, p, end - 1);
    }
}

/// The transcription's compound selector does not start at a combinator.
pub proof fn lemma_compound_not_at_comb(v: Seq<ComponentValue>, p: int, end: int, in_has: bool)
    requires
        0 <= p < end <= v.len(),
        i_comb_of(v[p]) is Some,
    ensures
        i_compound(v, p, end, cx0(), in_has) is None,
{
    lemma_type_selector(v, p, end);
    lemma_ident_at(v, p, end);
    lemma_delim_at(v, p, end, 0x2A);
    lemma_delim_at(v, p, end, 0x7C);
    assert(type_selector(v, p, end) is Absent);
    assert(i_type_selector(v, p, end, cx0()) == Some::<Option<(IType, int)>>(None));
    lemma_i_subs_stop(v, p, end, in_has, i_fuel(p, end));
}

/// The default namespace changes nothing when there is none.
pub proof fn lemma_default_ns_none(units: Seq<ICompound>, exempt: bool)
    ensures
        i_with_default_ns(units, cx0(), exempt) == units,
{
    assert(i_with_default_ns(units, cx0(), exempt) =~= units);
}

/// A complex selector the spec reads that has a transcription, the transcription reads.
pub proof fn lemma_complex_a(
    v: Seq<ComponentValue>,
    lo: int,
    hi: int,
    np: bool,
    exempt: bool,
    in_has: bool,
    c: Complex,
    m: IComplex,
)
    requires
        0 <= lo <= hi <= v.len(),
        no_fun(v, hi),
        complex_selector(v, lo, hi, np) == Some(c),
        rel_complex(c, m),
    ensures
        i_complex(v, lo, hi, cx0(), false, exempt, in_has) == Some(m),
{
    lemma_skip_same(v, lo, hi);
    let start = i_skip_ws(v, lo, hi);
    lemma_skip_ws(v, lo, hi);
    assert(start < hi);
    assert(complex_selector_loop(v, start, hi, Seq::empty(), Seq::empty(), np) == Some(c));
    assert(cloop_res(v, start, hi, Seq::empty(), Seq::empty(), np) == Some(c)) by {
        reveal(cloop_res);
    }
    assert(m.units.len() == c.compounds.len());
    assert(m.combs.len() == c.combinators.len());
    assert forall|j: int| 0 <= j < m.units.len() implies #[trigger] relc(c.compounds, 0, m.units, j) by {
        reveal(relc);
        assert(rel_compound(c.compounds[j], m.units[j]));
    }
    assert forall|j: int| 0 <= j < m.combs.len() implies #[trigger] relb(c.combinators, 0, m.combs, j) by {
        reveal(relb);
        assert(rel_comb(c.combinators[j], m.combs[j]));
    }
    lemma_units_a(v, start, hi, Seq::empty(), Seq::empty(), np, i_fuel(start, hi), c, m.units, m.combs, in_has);
    lemma_units_first(v, start, hi, Seq::empty(), Seq::empty(), np, c, m.units, in_has);
    assert(!i_is_ws(v[start]));
    lemma_trim_pos(v, start, hi);
    if i_comb_of(v[start]) is Some {
        lemma_compound_not_at_comb(v, start, hi, in_has);
    }
    lemma_default_ns_none(m.units, exempt);
    assert(m == (IComplex { lead: None, units: m.units, combs: m.combs }));
}

/// A complex selector the transcription reads, the spec reads too.
pub proof fn lemma_complex_b(
    v: Seq<ComponentValue>,
    lo: int,
    hi: int,
    np: bool,
    exempt: bool,
    in_has: bool,
    m: IComplex,
)
    requires
        0 <= lo <= hi <= v.len(),
        no_fun(v, hi),
        i_complex(v, lo, hi, cx0(), false, exempt, in_has) == Some(m),
    ensures
        complex_selector(v, lo, hi, np) is Some,
{
    lemma_skip_same(v, lo, hi);
    let start = i_skip_ws(v, lo, hi);
    lemma_skip_ws(v, lo, hi);
    let stop = i_trim_end(v, start, hi);
    assert(start < stop);
    assert(start < hi);
    match i_units(v, start, hi, cx0(), in_has, i_fuel(start, hi)) {
        Some((units, combs)) => {
            lemma_units_b(v, start, hi, Seq::empty(), Seq::empty(), np, i_fuel(start, hi), units, combs, in_has);
            assert(cloop_res(v, start, hi, Seq::empty(), Seq::empty(), np) is Some);
            reveal(cloop_res);
        },
        None => {},
    }
}


// ------------------------------------------------------------------------------------
// Selector lists
// ------------------------------------------------------------------------------------

/// The `j`-th transcribed complex selector is the counterpart of the `k + j`-th spec one.
#[verifier::opaque]
pub open spec fn relcx(l: Seq<Complex>, k: int, ml: Seq<IComplex>, j: int) -> bool {
    rel_complex(l[k + j], ml[j])
}

/// The spec's complex selector, opaque for the proofs about lists.
#[verifier::opaque]
pub open spec fn csel_res(v: Seq<ComponentValue>, lo: int, hi: int, np: bool) -> Option<Complex> {
    complex_selector(v, lo, hi, np)
}

/// The spec's loop over a list, opaque for the proofs about it.
#[verifier::opaque]
pub open spec fn clist_res(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>, np: bool) -> Option<
    Seq<Complex>,
> {
    complex_list_loop(v, i, hi, acc, np)
}

/// The spec's loop over a list, one step unfolded.
pub proof fn lemma_clist_unfold(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>, np: bool)
    ensures
        clist_res(v, i, hi, acc, np) == ({
            let comma = next_comma(v, i, hi);
            if i < 0 || comma < i || comma > hi {
                None
            } else {
                match csel_res(v, i, comma, np) {
                    None => None,
                    Some(selector) => if comma >= hi {
                        Some(acc.push(selector))
                    } else {
                        clist_res(v, comma + 1, hi, acc.push(selector), np)
                    },
                }
            }
        }),
{
    reveal_with_fuel(complex_list_loop, 2);
    reveal(clist_res);
    reveal(csel_res);
}

/// [`lemma_complex_a`], in terms of [`csel_res`].
pub proof fn lemma_complex_a_res(
    v: Seq<ComponentValue>,
    lo: int,
    hi: int,
    np: bool,
    exempt: bool,
    in_has: bool,
    c: Complex,
    m: IComplex,
)
    requires
        0 <= lo <= hi <= v.len(),
        no_fun(v, hi),
        csel_res(v, lo, hi, np) == Some(c),
        rel_complex(c, m),
    ensures
        i_complex(v, lo, hi, cx0(), false, exempt, in_has) == Some(m),
{
    reveal(csel_res);
    lemma_complex_a(v, lo, hi, np, exempt, in_has, c, m);
}

/// [`lemma_complex_b`], in terms of [`csel_res`].
pub proof fn lemma_complex_b_res(
    v: Seq<ComponentValue>,
    lo: int,
    hi: int,
    np: bool,
    exempt: bool,
    in_has: bool,
    m: IComplex,
)
    requires
        0 <= lo <= hi <= v.len(),
        no_fun(v, hi),
        i_complex(v, lo, hi, cx0(), false, exempt, in_has) == Some(m),
    ensures
        csel_res(v, lo, hi, np) is Some,
{
    reveal(csel_res);
    lemma_complex_b(v, lo, hi, np, exempt, in_has, m);
}

/// The loop over a list extends what was read before.
pub proof fn lemma_clist_prefix(v: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>, np: bool)
    requires
        0 <= i <= hi <= v.len(),
    ensures
        match clist_res(v, i, hi, acc, np) {
            Some(r) => r.len() >= acc.len() && r.subrange(0, acc.len() as int) == acc,
            None => true,
        },
    decreases hi - i,
{
    lemma_clist_unfold(v, i, hi, acc, np);
    lemma_comma_same(v, i, hi);
    lemma_comma(v, i, hi);
    let comma = next_comma(v, i, hi);
    if i >= 0 && comma >= i && comma <= hi {
        if let Some(sel) = csel_res(v, i, comma, np) {
            if comma < hi {
                let acc2 = acc.push(sel);
                lemma_clist_prefix(v, comma + 1, hi, acc2, np);
                if let Some(r) = clist_res(v, comma + 1, hi, acc2, np) {
                    assert(r.subrange(0, acc.len() as int) =~= acc);
                }
            }
        }
    }
}

/// The transcription's list, when the part before the comma is the last.
pub proof fn lemma_i_clist_last(v: Seq<ComponentValue>, p: int, end: int, exempt: bool, in_has: bool, c: IComplex)
    requires
        0 <= p <= end <= v.len(),
        i_comma(v, p, end) >= end,
        i_complex(v, p, i_comma(v, p, end), cx0(), false, exempt, in_has) == Some(c),
    ensures
        i_clist(v, p, end, cx0(), false, false, exempt, in_has) == Some(seq![c]),
{
    reveal_with_fuel(i_clist, 2);
}

/// The transcription's list, when there is more after the comma.
pub proof fn lemma_i_clist_step(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    exempt: bool,
    in_has: bool,
    c: IComplex,
    rest: Seq<IComplex>,
)
    requires
        0 <= p <= end <= v.len(),
        i_comma(v, p, end) < end,
        i_complex(v, p, i_comma(v, p, end), cx0(), false, exempt, in_has) == Some(c),
        i_clist(v, i_comma(v, p, end) + 1, end, cx0(), false, false, exempt, in_has) == Some(rest),
    ensures
        i_clist(v, p, end, cx0(), false, false, exempt, in_has) == Some(seq![c] + rest),
{
    reveal_with_fuel(i_clist, 2);
}

/// What the transcription's list did, when it succeeded.
pub proof fn lemma_i_clist_cases(v: Seq<ComponentValue>, p: int, end: int, exempt: bool, in_has: bool, ml: Seq<IComplex>)
    requires
        0 <= p <= end <= v.len(),
        i_clist(v, p, end, cx0(), false, false, exempt, in_has) == Some(ml),
    ensures
        ml.len() >= 1,
        i_complex(v, p, i_comma(v, p, end), cx0(), false, exempt, in_has) == Some(ml[0]),
        i_comma(v, p, end) >= end ==> ml.len() == 1,
        i_comma(v, p, end) < end ==> i_clist(
            v,
            i_comma(v, p, end) + 1,
            end,
            cx0(),
            false,
            false,
            exempt,
            in_has,
        ) == Some(ml.drop_first()),
{
    reveal_with_fuel(i_clist, 2);
    lemma_comma(v, p, end);
    let q = i_comma(v, p, end);
    if q < end {
        if let Some(rest) = i_clist(v, q + 1, end, cx0(), false, false, exempt, in_has) {
            if let Some(c) = i_complex(v, p, q, cx0(), false, exempt, in_has) {
                assert(ml =~= seq![c] + rest);
                assert(ml.drop_first() =~= rest);
            }
        }
    } else {
        if let Some(c) = i_complex(v, p, q, cx0(), false, exempt, in_has) {
            assert(ml =~= seq![c]);
        }
    }
}

/// A list the spec reads that has a transcription, the transcription reads.
#[verifier::rlimit(60)]
pub proof fn lemma_clist_a(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Complex>,
    np: bool,
    exempt: bool,
    in_has: bool,
    l: Seq<Complex>,
    ml: Seq<IComplex>,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        clist_res(v, p, end, acc, np) == Some(l),
        l.len() == acc.len() + ml.len(),
        forall|j: int| 0 <= j < ml.len() ==> #[trigger] relcx(l, acc.len() as int, ml, j),
    ensures
        i_clist(v, p, end, cx0(), false, false, exempt, in_has) == Some(ml),
    decreases end - p,
{
    lemma_clist_unfold(v, p, end, acc, np);
    lemma_comma_same(v, p, end);
    lemma_comma(v, p, end);
    let q = i_comma(v, p, end);
    assert(next_comma(v, p, end) == q);
    let k = acc.len() as int;
    if let Some(sel) = csel_res(v, p, q, np) {
        assert(no_fun(v, q));
        if q >= end {
            assert(l == acc.push(sel));
            assert(ml.len() == 1);
            assert(relcx(l, k, ml, 0));
            reveal(relcx);
            assert(rel_complex(sel, ml[0]));
            lemma_complex_a_res(v, p, q, np, exempt, in_has, sel, ml[0]);
            lemma_i_clist_last(v, p, end, exempt, in_has, ml[0]);
            assert(ml =~= seq![ml[0]]);
        } else {
            let acc2 = acc.push(sel);
            lemma_clist_prefix(v, q + 1, end, acc2, np);
            assert(l.subrange(0, acc2.len() as int) == acc2);
            assert(l.subrange(0, acc2.len() as int)[k] == l[k]);
            assert(l[k] == sel);
            assert(ml.len() >= 1);
            assert(relcx(l, k, ml, 0));
            reveal(relcx);
            assert(rel_complex(sel, ml[0]));
            lemma_complex_a_res(v, p, q, np, exempt, in_has, sel, ml[0]);
            let ml1 = ml.drop_first();
            assert forall|j: int| 0 <= j < ml1.len() implies #[trigger] relcx(l, acc2.len() as int, ml1, j) by {
                assert(ml1[j] == ml[j + 1]);
                assert(relcx(l, k, ml, j + 1));
                assert(l[k + (j + 1)] == l[acc2.len() as int + j]);
            }
            lemma_clist_a(v, q + 1, end, acc2, np, exempt, in_has, l, ml1);
            lemma_i_clist_step(v, p, end, exempt, in_has, ml[0], ml1);
            assert(ml =~= seq![ml[0]] + ml1);
        }
    }
}

/// A list the transcription reads, the spec reads too.
pub proof fn lemma_clist_b(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    acc: Seq<Complex>,
    np: bool,
    exempt: bool,
    in_has: bool,
    ml: Seq<IComplex>,
)
    requires
        0 <= p <= end <= v.len(),
        no_fun(v, end),
        i_clist(v, p, end, cx0(), false, false, exempt, in_has) == Some(ml),
    ensures
        clist_res(v, p, end, acc, np) is Some,
    decreases end - p,
{
    lemma_clist_unfold(v, p, end, acc, np);
    lemma_comma_same(v, p, end);
    lemma_comma(v, p, end);
    lemma_i_clist_cases(v, p, end, exempt, in_has, ml);
    let q = i_comma(v, p, end);
    assert(next_comma(v, p, end) == q);
    assert(no_fun(v, q));
    lemma_complex_b_res(v, p, q, np, exempt, in_has, ml[0]);
    if q < end {
        if let Some(sel) = csel_res(v, p, q, np) {
            lemma_clist_b(v, q + 1, end, acc.push(sel), np, exempt, in_has, ml.drop_first());
        }
    }
}

/// **Parsing, without functional pseudo-classes, spec to transcription.** If the spec parses a list
/// of component values with no function in it to a selector list that has a transcription, the
/// transcription parses the same list to that transcription.
pub proof fn theorem_parse_spec_to_transcription(v: Seq<ComponentValue>, l: Seq<Complex>, m: Seq<IComplex>)
    requires
        no_fun(v, v.len() as int),
        selector_list(v) == Some(l),
        rel_list(l, m),
    ensures
        i_parse_selector_list(v, cx0()) == Some(m),
{
    assert(complex_list_loop(v, 0, v.len() as int, Seq::empty(), false) == Some(l)) by {
        reveal_with_fuel(complex_list_loop, 2);
    }
    assert(clist_res(v, 0, v.len() as int, Seq::empty(), false) == Some(l)) by {
        reveal(clist_res);
    }
    assert forall|j: int| 0 <= j < m.len() implies #[trigger] relcx(l, 0, m, j) by {
        reveal(relcx);
        assert(rel_complex(l[j], m[j]));
    }
    lemma_clist_a(v, 0, v.len() as int, Seq::empty(), false, false, false, l, m);
}

/// **Parsing, without functional pseudo-classes, transcription to spec.** If the transcription
/// parses a list of component values with no function in it, the spec parses it too.
pub proof fn theorem_parse_transcription_to_spec(v: Seq<ComponentValue>, m: Seq<IComplex>)
    requires
        no_fun(v, v.len() as int),
        i_parse_selector_list(v, cx0()) == Some(m),
    ensures
        selector_list(v) is Some,
{
    lemma_clist_b(v, 0, v.len() as int, Seq::empty(), false, false, false, m);
    reveal(clist_res);
    reveal_with_fuel(complex_list_loop, 2);
}

} // verus!
