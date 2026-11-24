//! CSSOM "serialize a group of selectors", for parsed selectors.
//!
//! Each function is the spec function of the same name in [`super::spec`], and is proven to
//! append exactly what that function gives: `put_identifier`, `put_string` and
//! `put_code_point` equal CSSOM's escaping, and `put_simple`, `put_compound`, `put_complex`
//! and `put_list` the serialization of the view of what they are given. [`serialize`]
//! ensures [`super::contract::serialize_ensures`] of the view of its argument, when the
//! argument's ranges and its list are well-formed (`ranges_wf` and `list_wf`), which every
//! result of `parse_selector` is (`exec_check`). The `<an+b>` part is `clazel-css`'s
//! `write_a_n_plus_b`, proven equal to its spec there.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::exec_match::{lemma_compound_wf_at, lemma_compounds_wf_at, lemma_list_wf_at};
use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use clazel_css::parser::exec_anb::view_integer;
use clazel_css::parser::exec_anb::{ExecInteger, write_a_n_plus_b};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Appends `text`.
fn put(out: &mut Vec<u32>, text: &[u32])
    ensures
        final(out)@ == old(out)@ + text@,
{
    out.extend_from_slice(text);
}

/// The lowercase hexadecimal digit of `d`, below 16.
fn hex_digit_of(d: u32) -> (r: u32)
    requires
        d < 16,
    ensures
        r == hex_digit(d as nat),
{
    if d < 10 {
        0x30u32.saturating_add(d)
    } else {
        0x57u32.saturating_add(d)
    }
}

/// One step of `hex_digits`.
proof fn lemma_hex_digits_step(v: u32, acc: Seq<u32>)
    requires
        v >= 16,
    ensures
        hex_digits(v as nat, acc) == hex_digits((v / 16) as nat, seq![hex_digit((v % 16) as nat)] + acc),
{
    assert((v as nat) / 16 == (v / 16) as nat);
    assert((v as nat) % 16 == (v % 16) as nat);
}

/// [`escape_as_code_point`].
fn put_code_point(out: &mut Vec<u32>, c: u32)
    ensures
        final(out)@ == old(out)@ + escape_as_code_point(c),
{
    let ghost start = out@;
    out.push(0x5C);
    let mut digits: Vec<u32> = Vec::new();
    let mut v = c;
    loop
        invariant_except_break
            hex_digits(c as nat, Seq::empty()) == hex_digits(v as nat, digits@.reverse()),
        ensures
            hex_digits(c as nat, Seq::empty()) == digits@.reverse(),
        decreases v,
    {
        let ghost before = digits@;
        let d = hex_digit_of(v % 16);
        digits.push(d);
        proof {
            assert(digits@.reverse() =~= seq![d] + before.reverse());
        }
        if v < 16 {
            proof {
                assert((v as nat) < 16);
                assert(v % 16 == v);
                assert(hex_digits(v as nat, before.reverse()) == seq![hex_digit(v as nat)] + before.reverse());
            }
            break;
        }
        proof {
            lemma_hex_digits_step(v, before.reverse());
        }
        v /= 16;
    }
    let mut k = digits.len();
    proof {
        assert(out@ == start.push(0x5C));
    }
    while k > 0
        invariant
            k <= digits@.len(),
            out@ == start + seq![0x5Cu32] + digits@.reverse().subrange(0, (digits@.len() - k) as int),
        decreases k,
    {
        k = k.saturating_sub(1);
        let x = *item(digits.as_slice(), k);
        out.push(x);
        proof {
            let n = digits@.len() as int;
            let r = digits@.reverse();
            assert(r[n - k as int - 1] == digits@[k as int]);
            assert(r.subrange(0, n - k as int) =~= r.subrange(0, n - k as int - 1).push(x));
        }
    }
    out.push(0x20);
    proof {
        let r = digits@.reverse();
        assert(r.subrange(0, digits@.len() as int) =~= r);
        assert(out@ =~= start + escape_as_code_point(c));
    }
}

/// CSSOM "serialize an identifier".
fn put_identifier(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + serialize_an_identifier(s@),
{
    let ghost start = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            out@ == start + identifier_prefix(s@, i as int),
        decreases s.len() - i,
    {
        let c = *item(s, i);
        proof {
            assert(identifier_prefix(s@, i as int + 1) == identifier_prefix(s@, i as int) + identifier_char(s@, i as int));
        }
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
        proof {
            assert(out@ =~= start + identifier_prefix(s@, i as int + 1));
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(identifier_prefix(s@, s@.len() as int) == serialize_an_identifier(s@));
    }
}

/// CSS Syntax's "non-ASCII ident code point".
fn is_non_ascii_ident_code_point_exec(c: u32) -> (r: bool)
    ensures
        r == is_non_ascii_ident(c),
{
    c == 0xB7 || (0xC0..=0xD6).contains(&c) || (0xD8..=0xF6).contains(&c) || (0xF8..=0x37D).contains(
        &c,
    ) || (0x37F..=0x1FFF).contains(&c) || c == 0x200C || c == 0x200D || c == 0x203F || c
        == 0x2040 || (0x2070..=0x218F).contains(&c) || (0x2C00..=0x2FEF).contains(&c) || (0x3001
        ..=0xD7FF).contains(&c) || (0xF900..=0xFDCF).contains(&c) || (0xFDF0..=0xFFFD).contains(
        &c,
    ) || (0x1_0000..=0x10_FFFF).contains(&c)
}

/// CSSOM "serialize a string".
fn put_string(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + serialize_a_string(s@),
{
    let ghost start = out@;
    out.push(0x22);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            out@ == start + seq![0x22u32] + string_prefix(s@, i as int),
        decreases s.len() - i,
    {
        let c = *item(s, i);
        proof {
            assert(string_prefix(s@, i as int + 1) == string_prefix(s@, i as int) + string_char(s@[i as int]));
        }
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
        proof {
            assert(out@ =~= start + seq![0x22u32] + string_prefix(s@, i as int + 1));
        }
        i = i.saturating_add(1);
    }
    out.push(0x22);
    proof {
        assert(out@ =~= start + serialize_a_string(s@));
    }
}

/// The name of a pseudo-class without an argument ([`pseudo_class_name`]).
fn pseudo_class_text(class: PseudoClass) -> (r: &'static [u32])
    ensures
        r@ == pseudo_class_name(class),
{
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
        PseudoClass::Scope => &[0x73, 0x63, 0x6F, 0x70, 0x65],
    }
}

/// [`pseudo_element_name`].
fn pseudo_element_text(element: PseudoElement) -> (r: &'static [u32])
    ensures
        r@ == pseudo_element_name(element),
{
    match element {
        PseudoElement::Before => &[0x62, 0x65, 0x66, 0x6F, 0x72, 0x65],
        PseudoElement::After => &[0x61, 0x66, 0x74, 0x65, 0x72],
        PseudoElement::FirstLine => &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x69, 0x6E, 0x65],
        PseudoElement::FirstLetter => &[0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x65, 0x74, 0x74, 0x65, 0x72],
    }
}

/// [`nth_name`].
fn nth_text(kind: NthKind) -> (r: &'static [u32])
    ensures
        r@ == nth_name(kind),
{
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
fn matcher_of(matcher: AttrMatcher) -> (r: &'static [u32])
    ensures
        r@ == matcher_text(matcher),
{
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
fn integer(v: i32) -> (r: ExecInteger)
    ensures
        view_integer(r) == v as int,
{
    if v < 0 {
        let m: i64 = match 0i64.checked_sub(v as i64) {
            Some(m) => m,
            None => vstd::pervasive::unreached(),
        };
        ExecInteger { negative: true, magnitude: m as u64 }
    } else {
        ExecInteger { negative: false, magnitude: v as u64 }
    }
}

/// Appends the text of a combinator.
fn put_combinator(out: &mut Vec<u32>, c: Combinator)
    ensures
        final(out)@ == old(out)@ + combinator_text(c),
{
    match c {
        Combinator::Descendant => out.push(0x20),
        Combinator::Child => put(out, &[0x20, 0x3E, 0x20]),
        Combinator::NextSibling => put(out, &[0x20, 0x2B, 0x20]),
        Combinator::SubsequentSibling => put(out, &[0x20, 0x7E, 0x20]),
    }
    proof {
        let t = combinator_text(c);
        assert(final(out)@ =~= old(out)@ + t);
    }
}

/// [`serialize_a_simple_selector`] of the simple selector at `si`, in the list `bound`.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
fn put_simple(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, si: usize)
    requires
        ranges_wf(*s),
        bound <= s.lists@.len(),
        si < s.simples@.len(),
        simple_wf(view_simple(*s, bound as int, si as int)),
    ensures
        final(out)@ == old(out)@ + serialize_a_simple_selector(view_simple(*s, bound as int, si as int)),
    decreases bound, 0int,
{
    let ghost start = out@;
    let ghost v = view_simple(*s, bound as int, si as int);
    match item(s.simples.as_slice(), si) {
        ExecSimple::Type { ns, name } => {
            proof {
                assert(v == Simple::Type { ns: *ns, name: name@ });
            }
            if matches!(*ns, NsPrefix::NoNamespace) {
                out.push(0x7C);
            }
            put_identifier(out, name);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Universal { ns } => {
            if matches!(*ns, NsPrefix::NoNamespace) {
                out.push(0x7C);
            }
            out.push(0x2A);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Attribute { ns, name, test } => {
            proof {
                assert(v == Simple::Attribute { ns: *ns, name: name@, test: view_test(*test) });
            }
            out.push(0x5B);
            if matches!(*ns, NsPrefix::Any) {
                put(out, &[0x2A, 0x7C]);
            }
            put_identifier(out, name);
            let ghost before_value = out@;
            if let Some(t) = test {
                put(out, matcher_of(t.matcher));
                put_string(out, &t.value);
                let ghost before_flag = out@;
                match t.flag {
                    Some(CaseFlag::I) => put(out, &[0x20, 0x69]),
                    Some(CaseFlag::S) => put(out, &[0x20, 0x73]),
                    None => {},
                }
                proof {
                    assert(out@ =~= before_value + matcher_text(t.matcher) + serialize_a_string(t.value@) + match t.flag {
                        None => Seq::empty(),
                        Some(CaseFlag::I) => seq![0x20u32, 0x69],
                        Some(CaseFlag::S) => seq![0x20u32, 0x73],
                    });
                }
            }
            out.push(0x5D);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Class { name } => {
            out.push(0x2E);
            put_identifier(out, name);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Id { name } => {
            out.push(0x23);
            put_identifier(out, name);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::PseudoClass { class } => {
            out.push(0x3A);
            put(out, pseudo_class_text(*class));
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Nth { kind, a, b } => {
            out.push(0x3A);
            put(out, nth_text(*kind));
            out.push(0x28);
            let text = write_a_n_plus_b(integer(*a), integer(*b));
            put(out, &text);
            out.push(0x29);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Is { list } => {
            put(out, &[0x3A, 0x69, 0x73, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Where { list } => {
            put(out, &[0x3A, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::Not { list } => {
            put(out, &[0x3A, 0x6E, 0x6F, 0x74, 0x28]);
            if *list < bound {
                put_list(out, s, *list);
            }
            out.push(0x29);
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
        ExecSimple::PseudoElement { element } => {
            put(out, &[0x3A, 0x3A]);
            put(out, pseudo_element_text(*element));
            proof {
                assert(out@ =~= start + serialize_a_simple_selector(v));
            }
        },
    }
}

/// [`is_omitted_universal`] of the selector `x` stands for.
spec fn omitted_view(x: ExecSimple) -> bool {
    match x {
        ExecSimple::Universal { ns } => ns != NsPrefix::NoNamespace,
        _ => false,
    }
}

/// [`is_omitted_universal`].
fn omitted(x: &ExecSimple) -> (r: bool)
    ensures
        r == omitted_view(*x),
{
    match x {
        ExecSimple::Universal { ns } => {
            !matches!(*ns, NsPrefix::NoNamespace)
        },
        _ => false,
    }
}

/// [`serialize_compound`] of the compound selector at `ci`.
fn put_compound(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, ci: usize)
    requires
        ranges_wf(*s),
        bound <= s.lists@.len(),
        ci < s.compounds@.len(),
        compound_wf(view_compound(*s, bound as int, ci as int), view_compound(*s, bound as int, ci as int).len() as int),
    ensures
        final(out)@ == old(out)@ + serialize_compound(view_compound(*s, bound as int, ci as int)),
    decreases bound, 1int,
{
    let ghost start = out@;
    let ghost v = view_compound(*s, bound as int, ci as int);
    proof {
        lemma_view_compound(*s, bound as int, ci as int);
    }
    let r = *item(s.compounds.as_slice(), ci);
    let hi = r.hi;
    let lo = r.lo;
    proof {
        assert(lo <= hi <= s.simples@.len());
    }
    if hi == lo.saturating_add(1) && matches!(item(s.simples.as_slice(), lo), ExecSimple::Universal { .. }) {
        proof {
            assert(v.len() == 1);
            lemma_compound_wf_at(v, 1, 0);
            assert(v[0] == view_simple(*s, bound as int, lo as int));
            assert(v[0] is Universal);
        }
        put_simple(out, s, bound, lo);
        proof {
            assert(serialize_compound(v) == serialize_a_simple_selector(v[0]));
            assert(out@ =~= start + serialize_compound(v));
        }
        return;
    }
    proof {
        assert(!(v.len() == 1 && v[0] is Universal));
    }
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            bound <= s.lists@.len(),
            lo <= k <= hi,
            hi <= s.simples@.len(),
            v == view_compound(*s, bound as int, ci as int),
            v.len() == hi - lo,
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_simple(*s, bound as int, lo + j),
            compound_wf(v, v.len() as int),
            out@ == start + compound_text(v, (k - lo) as int),
        decreases hi - k,
    {
        proof {
            lemma_compound_wf_at(v, v.len() as int, (k - lo) as int);
            assert(v[(k - lo) as int] == view_simple(*s, bound as int, k as int));
        }
        let x = item(s.simples.as_slice(), k);
        if !omitted(x) {
            put_simple(out, s, bound, k);
            proof {
                assert(out@ =~= start + compound_text(v, (k - lo) as int + 1));
            }
        } else {
            proof {
                assert(out@ =~= start + compound_text(v, (k - lo) as int + 1));
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(compound_text(v, v.len() as int) == serialize_compound(v));
    }
}

/// [`serialize_chain`] of the complex selector at `ci`.
fn put_complex(out: &mut Vec<u32>, s: &ExecSelectors, bound: usize, ci: usize)
    requires
        ranges_wf(*s),
        bound <= s.lists@.len(),
        ci < s.complexes@.len(),
        complex_wf(view_complex(*s, bound as int, ci as int)),
    ensures
        final(out)@ == old(out)@ + serialize_a_selector(view_complex(*s, bound as int, ci as int)),
    decreases bound, 2int,
{
    let ghost start = out@;
    let ghost c = view_complex(*s, bound as int, ci as int);
    let cx = *item(s.complexes.as_slice(), ci);
    proof {
        lemma_view_complex(*s, bound as int, ci as int);
        assert(cx == s.complexes@[ci as int]);
    }
    let hi = cx.compounds.hi;
    let lo = cx.compounds.lo;
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            bound <= s.lists@.len(),
            cx == s.complexes@[ci as int],
            c == view_complex(*s, bound as int, ci as int),
            complex_wf(c),
            lo == cx.compounds.lo,
            hi == cx.compounds.hi,
            c.compounds.len() == hi - lo,
            c.combinators.len() + 1 == hi - lo,
            hi <= s.compounds@.len(),
            lo <= k <= hi,
            forall|j: int| 0 <= j < c.compounds.len() ==> #[trigger] c.compounds[j] == view_compound(*s, bound as int, lo + j),
            forall|j: int| 0 <= j < c.combinators.len() ==> #[trigger] c.combinators[j] == s.combinators@[cx.combinators.lo + j],
            cx.combinators.lo + c.combinators.len() <= s.combinators@.len(),
            out@ == start + serialize_chain(c, (k - lo) as int),
        decreases hi - k,
    {
        proof {
            lemma_compounds_wf_at(c, c.compounds.len() as int, (k - lo) as int);
        }
        if k > lo {
            let j = cx.combinators.lo.saturating_add(k.saturating_sub(lo)).saturating_sub(1);
            proof {
                assert(j == cx.combinators.lo + (k - lo) - 1);
                assert(j < s.combinators@.len());
                assert(c.combinators[(k - lo - 1) as int] == s.combinators@[j as int]);
            }
            put_combinator(out, *item(s.combinators.as_slice(), j));
        }
        put_compound(out, s, bound, k);
        proof {
            let n = (k - lo) as int + 1;
            assert(serialize_chain(c, n) == (if n == 1 {
                serialize_compound(c.compounds[0])
            } else {
                serialize_chain(c, n - 1) + combinator_text(c.combinators[n - 2]) + serialize_compound(c.compounds[n - 1])
            }));
            assert(out@ =~= start + serialize_chain(c, n));
        }
        k = k.saturating_add(1);
    }
}

/// [`serialize_list`] of the list at `li`.
fn put_list(out: &mut Vec<u32>, s: &ExecSelectors, li: usize)
    requires
        ranges_wf(*s),
        li < s.lists@.len(),
        list_wf(view_list(*s, li as int), view_list(*s, li as int).len() as int),
    ensures
        final(out)@ == old(out)@ + serialize_list(view_list(*s, li as int), view_list(*s, li as int).len() as int),
    decreases li, 3int,
{
    let ghost start = out@;
    let ghost v = view_list(*s, li as int);
    proof {
        lemma_view_list(*s, li as int);
    }
    let r = *item(s.lists.as_slice(), li);
    let hi = r.hi;
    let lo = r.lo;
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            li < s.lists@.len(),
            r == s.lists@[li as int],
            lo == r.lo,
            hi == r.hi,
            hi <= s.complexes@.len(),
            lo <= k <= hi,
            v == view_list(*s, li as int),
            v.len() == hi - lo,
            list_wf(v, v.len() as int),
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_complex(*s, li as int, lo + j),
            out@ == start + serialize_list(v, (k - lo) as int),
        decreases hi - k,
    {
        proof {
            lemma_list_wf_at(v, v.len() as int, (k - lo) as int);
        }
        if k > lo {
            put(out, &[0x2C, 0x20]);
        }
        put_complex(out, s, li, k);
        proof {
            let n = (k - lo) as int + 1;
            assert(serialize_list(v, n) == (if n == 1 {
                serialize_chain(v[0], v[0].compounds.len() as int)
            } else {
                serialize_list(v, n - 1) + seq![0x2Cu32, 0x20] + serialize_chain(v[n - 1], v[n - 1].compounds.len() as int)
            }));
            assert(out@ =~= start + serialize_list(v, n));
        }
        k = k.saturating_add(1);
    }
}

/// CSSOM "serialize a group of selectors" of the result of a parse.
pub fn serialize(s: &ExecSelectors) -> (r: Vec<u32>)
    requires
        ranges_wf(*s),
        list_wf(view_selectors(*s), view_selectors(*s).len() as int),
    ensures
        serialize_ensures(view_selectors(*s), r@),
{
    let mut out: Vec<u32> = Vec::new();
    if !s.lists.is_empty() {
        put_list(&mut out, s, s.lists.len().saturating_sub(1));
    }
    proof {
        if s.lists@.len() == 0 {
            assert(view_selectors(*s) =~= Seq::<Complex>::empty());
        }
        assert(out@ =~= serialize_a_group_of_selectors(view_selectors(*s)));
    }
    out
}

} // verus!
