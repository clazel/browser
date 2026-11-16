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

} // verus!
