//! CSSOM "serialize a group of selectors", for parsed selectors.
//!
//! Each function is the spec function of the same name in [`super::spec`]. Verus checks that
//! it never panics, overflows or loops forever; that it returns what the spec does is **not
//! yet proven** ([`super::contract::serialize_ensures`] is stated and unmet), and the WPT
//! parsing cases are the evidence for now.

use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_css::parser::exec_anb::{ExecInteger, write_a_n_plus_b};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Appends `text`.
fn put(out: &mut Vec<u32>, text: &[u32]) {
    out.extend_from_slice(text);
}

/// The lowercase hexadecimal digit of `d`, below 16.
fn hex_digit_of(d: u32) -> u32 {
    if d < 10 {
        0x30u32.saturating_add(d)
    } else {
        0x57u32.saturating_add(d)
    }
}

/// [`escape_as_code_point`].
fn put_code_point(out: &mut Vec<u32>, c: u32) {
    out.push(0x5C);
    let mut digits: Vec<u32> = Vec::new();
    let mut v = c;
    loop
        decreases v,
    {
        digits.push(hex_digit_of(v % 16));
        if v < 16 {
            break;
        }
        v /= 16;
    }
    let mut k = digits.len();
    while k > 0
        invariant
            k <= digits@.len(),
        decreases k,
    {
        k = k.saturating_sub(1);
        out.push(*item(digits.as_slice(), k));
    }
    out.push(0x20);
}

/// CSSOM "serialize an identifier".
fn put_identifier(out: &mut Vec<u32>, s: &[u32]) {
    let mut i: usize = 0;
    while i < s.len()
        decreases s.len() - i,
    {
        let c = *item(s, i);
        if c == 0 {
            out.push(0xFFFD);
        } else if (0x01..=0x1F).contains(&c) || c == 0x7F || (i == 0 && (0x30..=0x39).contains(&c))
            || (i == 1 && (0x30..=0x39).contains(&c) && *item(s, 0) == 0x2D) {
            // A control; a digit first; a digit second, after "-": "escaped as code point".
            put_code_point(out, c);
        } else if i == 0 && c == 0x2D && s.len() == 1 {
            out.push(0x5C);
            out.push(c);
        } else if is_non_ascii_ident_code_point_exec(c) || c == 0x2D || c == 0x5F || (0x30..=0x39).contains(
            &c,
        ) || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) {
            out.push(c);
        } else {
            out.push(0x5C);
            out.push(c);
        }
        i = i.saturating_add(1);
    }
}

/// CSS Syntax's "non-ASCII ident code point".
fn is_non_ascii_ident_code_point_exec(c: u32) -> bool {
    c == 0xB7 || (0xC0..=0xD6).contains(&c) || (0xD8..=0xF6).contains(&c) || (0xF8..=0x37D).contains(
        &c,
    ) || (0x37F..=0x1FFF).contains(&c) || c == 0x200C || c == 0x200D || c == 0x203F || c
        == 0x2040 || (0x2070..=0x218F).contains(&c) || (0x2C00..=0x2FEF).contains(&c) || (0x3001
        ..=0xD7FF).contains(&c) || (0xF900..=0xFDCF).contains(&c) || (0xFDF0..=0xFFFD).contains(
        &c,
    ) || (0x1_0000..=0x10_FFFF).contains(&c)
}

/// CSSOM "serialize a string".
fn put_string(out: &mut Vec<u32>, s: &[u32]) {
    out.push(0x22);
    let mut i: usize = 0;
    while i < s.len()
        decreases s.len() - i,
    {
        let c = *item(s, i);
        if c == 0 {
            out.push(0xFFFD);
        } else if (0x01..=0x1F).contains(&c) || c == 0x7F {
            put_code_point(out, c);
        } else if c == 0x22 || c == 0x5C {
            out.push(0x5C);
            out.push(c);
        } else {
            out.push(c);
        }
        i = i.saturating_add(1);
    }
    out.push(0x22);
}

/// The name of a pseudo-class without an argument ([`pseudo_class_name`]).
fn pseudo_class_text(class: PseudoClass) -> &'static [u32] {
    match class {
        PseudoClass::Link => &[0x6C, 0x69, 0x6E, 0x6B],
        PseudoClass::Visited => &[0x76, 0x69, 0x73, 0x69, 0x74, 0x65, 0x64],
        PseudoClass::AnyLink => &[0x61, 0x6E, 0x79, 0x2D, 0x6C, 0x69, 0x6E, 0x6B],
        PseudoClass::Root => &[0x72, 0x6F, 0x6F, 0x74],
        PseudoClass::Empty => &[0x65, 0x6D, 0x70, 0x74, 0x79],
        PseudoClass::FirstChild => &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        PseudoClass::LastChild => &[0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        PseudoClass::OnlyChild => &[0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        PseudoClass::FirstOfType => &[
            0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65,
        ],
        PseudoClass::LastOfType => &[0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
        PseudoClass::OnlyOfType => &[0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
        PseudoClass::Hover => &[0x68, 0x6F, 0x76, 0x65, 0x72],
        PseudoClass::Active => &[0x61, 0x63, 0x74, 0x69, 0x76, 0x65],
        PseudoClass::Focus => &[0x66, 0x6F, 0x63, 0x75, 0x73],
        PseudoClass::FocusVisible => &[
            0x66, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x76, 0x69, 0x73, 0x69, 0x62, 0x6C, 0x65,
        ],
        PseudoClass::FocusWithin => &[0x66, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x77, 0x69, 0x74, 0x68, 0x69, 0x6E],
    }
}

/// [`pseudo_element_name`].
fn pseudo_element_text(element: PseudoElement) -> &'static [u32] {
    match element {
        PseudoElement::Before => &[0x62, 0x65, 0x66, 0x6F, 0x72, 0x65],
        PseudoElement::After => &[0x61, 0x66, 0x74, 0x65, 0x72],
        PseudoElement::FirstLine => &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x69, 0x6E, 0x65],
        PseudoElement::FirstLetter => &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x65, 0x74, 0x74, 0x65, 0x72],
    }
}

/// [`nth_name`].
fn nth_text(kind: NthKind) -> &'static [u32] {
    match kind {
        NthKind::Child => &[0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        NthKind::LastChild => &[0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        NthKind::OfType => &[0x6E, 0x74, 0x68, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
        NthKind::LastOfType => &[
            0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70,
            0x65,
        ],
    }
}

/// [`matcher_text`].
fn matcher_of(matcher: AttrMatcher) -> &'static [u32] {
    match matcher {
        AttrMatcher::Equals => &[0x3D],
        AttrMatcher::Includes => &[0x7E, 0x3D],
        AttrMatcher::DashMatch => &[0x7C, 0x3D],
        AttrMatcher::Prefix => &[0x5E, 0x3D],
        AttrMatcher::Suffix => &[0x24, 0x3D],
        AttrMatcher::Substring => &[0x2A, 0x3D],
    }
}

/// An `i32` as sign and magnitude.
fn integer(v: i32) -> ExecInteger {
    if v < 0 {
        ExecInteger { negative: true, magnitude: 0i64.wrapping_sub(v as i64) as u64 }
    } else {
        ExecInteger { negative: false, magnitude: v as u64 }
    }
}

/// [`serialize_a_simple_selector`] of the simple selector at `si`, in the list `bound`.
fn put_simple(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, si: usize)
    requires
        si < s.simples@.len(),
    decreases bound, 0int,
{
    match item(s.simples.as_slice(), si) {
        ExecSimple::Type { ns, name } => {
            if *ns == NsPrefix::NoNamespace {
                out.push(0x7C);
            }
            put_identifier(out, name);
        },
        ExecSimple::Universal { ns } => {
            if *ns == NsPrefix::NoNamespace {
                out.push(0x7C);
            }
            out.push(0x2A);
        },
        ExecSimple::Attribute { ns, name, test } => {
            out.push(0x5B);
            if *ns == NsPrefix::Any {
                put(out, &[0x2A, 0x7C]);
            }
            put_identifier(out, name);
            if let Some(t) = test {
                put(out, matcher_of(t.matcher));
                put_string(out, &t.value);
                match t.flag {
                    Some(CaseFlag::I) => put(out, &[0x20, 0x69]),
                    Some(CaseFlag::S) => put(out, &[0x20, 0x73]),
                    None => {},
                }
            }
            out.push(0x5D);
        },
        ExecSimple::Class { name } => {
            out.push(0x2E);
            put_identifier(out, name);
        },
        ExecSimple::Id { name } => {
            out.push(0x23);
            put_identifier(out, name);
        },
        ExecSimple::PseudoClass { class } => {
            out.push(0x3A);
            put(out, pseudo_class_text(*class));
        },
        ExecSimple::Nth { kind, a, b } => {
            out.push(0x3A);
            put(out, nth_text(*kind));
            out.push(0x28);
            let text = write_a_n_plus_b(integer(*a), integer(*b));
            put(out, &text);
            out.push(0x29);
        },
        ExecSimple::Is { list } => {
            put(out, &[0x3A, 0x69, 0x73, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
        },
        ExecSimple::Where { list } => {
            put(out, &[0x3A, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
        },
        ExecSimple::Not { list } => {
            put(out, &[0x3A, 0x6E, 0x6F, 0x74, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
        },
        ExecSimple::PseudoElement { element } => {
            put(out, &[0x3A, 0x3A]);
            put(out, pseudo_element_text(*element));
        },
    }
}

/// [`is_omitted_universal`].
fn omitted(x: &ExecSimple) -> bool {
    matches!(x, ExecSimple::Universal { ns } if *ns != NsPrefix::NoNamespace)
}

/// [`serialize_compound`] of the compound selector at `ci`.
fn put_compound(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, ci: usize)
    requires
        ci < s.compounds@.len(),
    decreases bound, 1int,
{
    let r = *item(s.compounds.as_slice(), ci);
    let hi = if r.hi <= s.simples.len() {
        r.hi
    } else {
        s.simples.len()
    };
    let lo = r.lo;
    if hi == lo.saturating_add(1) && lo < hi && matches!(item(s.simples.as_slice(), lo), ExecSimple::Universal { .. }) {
        put_simple(out, s, bound, lo);
        return;
    }
    let mut k = lo;
    while k < hi
        invariant
            hi <= s.simples@.len(),
        decreases hi - k,
    {
        if !omitted(item(s.simples.as_slice(), k)) {
            put_simple(out, s, bound, k);
        }
        k = k.saturating_add(1);
    }
}

/// [`serialize_chain`] of the complex selector at `ci`.
fn put_complex(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, ci: usize)
    requires
        ci < s.complexes@.len(),
    decreases bound, 2int,
{
    let c = *item(s.complexes.as_slice(), ci);
    let hi = if c.compounds.hi <= s.compounds.len() {
        c.compounds.hi
    } else {
        s.compounds.len()
    };
    let mut k = c.compounds.lo;
    while k < hi
        invariant
            hi <= s.compounds@.len(),
        decreases hi - k,
    {
        if k > c.compounds.lo {
            let j = c.combinators.lo.saturating_add(k.saturating_sub(c.compounds.lo)).saturating_sub(1);
            if j < s.combinators.len() {
                match item(s.combinators.as_slice(), j) {
                    Combinator::Descendant => out.push(0x20),
                    Combinator::Child => put(out, &[0x20, 0x3E, 0x20]),
                    Combinator::NextSibling => put(out, &[0x20, 0x2B, 0x20]),
                    Combinator::SubsequentSibling => put(out, &[0x20, 0x7E, 0x20]),
                }
            }
        }
        put_compound(out, s, bound, k);
        k = k.saturating_add(1);
    }
}

/// [`serialize_list`] of the list at `li`.
fn put_list(out: &mut Vec<u32>, s: &ExecSelectors, li: usize)
    decreases li, 3int,
{
    if li >= s.lists.len() {
        return;
    }
    let r = *item(s.lists.as_slice(), li);
    let hi = if r.hi <= s.complexes.len() {
        r.hi
    } else {
        s.complexes.len()
    };
    let mut k = r.lo;
    while k < hi
        invariant
            hi <= s.complexes@.len(),
        decreases hi - k,
    {
        if k > r.lo {
            put(out, &[0x2C, 0x20]);
        }
        put_complex(out, s, li, k);
        k = k.saturating_add(1);
    }
}

/// CSSOM "serialize a group of selectors" of the result of a parse.
pub fn serialize(s: &ExecSelectors) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    if !s.lists.is_empty() {
        put_list(&mut out, s, s.lists.len().saturating_sub(1));
    }
    out
}

} // verus!
