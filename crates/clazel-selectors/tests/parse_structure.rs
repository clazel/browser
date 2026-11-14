//! What `parse_selector` builds, checked without the serializer.
//!
//! `tests/conformance_selectors.rs` checks the parser only as `serialize(parse(x))`, through
//! two functions that no proof ties to the spec. Here a test-owned decoder walks the arrays
//! of an `ExecSelectors` by their ranges into a tree of this file's own types, and each case
//! compares that tree with one written by hand from the Selectors Level 4 grammar (§18, the
//! productions are cited per group), and from CSS Syntax for tokens and `<an+b>`.
//!
//! The expected trees come from the standard, not from what the parser returned. Where this
//! UA is narrower than the standard (a named namespace prefix is undeclared, so invalid;
//! `of S` and unsupported pseudo-classes are invalid), the case says so.

use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_types::{ExecRange, ExecSelectors, ExecSimple};
use clazel_selectors::spec::{
    AttrMatcher, CaseFlag, Combinator, NsPrefix, NthKind, PseudoClass, PseudoElement,
};

// ------------------------------------------------------------------------------------
// The tree the decoder builds and the cases are written in
// ------------------------------------------------------------------------------------

/// A simple selector, with names as text.
#[derive(Debug, Clone, PartialEq, Eq)]
enum S {
    Type(NsPrefix, String),
    Universal(NsPrefix),
    Id(String),
    Class(String),
    Attr(
        NsPrefix,
        String,
        Option<(AttrMatcher, String, Option<CaseFlag>)>,
    ),
    Pc(PseudoClass),
    Nth(NthKind, i32, i32),
    Is(Vec<Cx>),
    Where(Vec<Cx>),
    Not(Vec<Cx>),
    Pe(PseudoElement),
}

/// A complex selector: compounds, and the combinators between them.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Cx {
    compounds: Vec<Vec<S>>,
    combinators: Vec<Combinator>,
}

fn name(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// What the decoder puts in the tree where an index is out of bounds, so that the case fails
/// with a readable difference (the parser's arrays are in bounds, `ranges_wf`).
fn broken(what: &str) -> S {
    S::Type(NsPrefix::Absent, format!("<out of bounds: {what}>"))
}

fn slice<T>(v: &[T], r: ExecRange) -> &[T] {
    v.get(r.lo..r.hi).unwrap_or_default()
}

fn decode_simple(s: &ExecSelectors, si: usize) -> S {
    let Some(simple) = s.simples.get(si) else {
        return broken("simple");
    };
    match simple {
        ExecSimple::Type { ns, name: n } => S::Type(*ns, name(n)),
        ExecSimple::Universal { ns } => S::Universal(*ns),
        ExecSimple::Id { name: n } => S::Id(name(n)),
        ExecSimple::Class { name: n } => S::Class(name(n)),
        ExecSimple::Attribute { ns, name: n, test } => S::Attr(
            *ns,
            name(n),
            test.as_ref().map(|t| (t.matcher, name(&t.value), t.flag)),
        ),
        ExecSimple::PseudoClass { class } => S::Pc(*class),
        ExecSimple::Nth { kind, a, b } => S::Nth(*kind, *a, *b),
        ExecSimple::Is { list } => S::Is(decode_list(s, *list)),
        ExecSimple::Where { list } => S::Where(decode_list(s, *list)),
        ExecSimple::Not { list } => S::Not(decode_list(s, *list)),
        ExecSimple::PseudoElement { element } => S::Pe(*element),
    }
}

fn decode_complex(s: &ExecSelectors, ci: usize) -> Cx {
    let Some(c) = s.complexes.get(ci) else {
        return Cx {
            compounds: vec![vec![broken("complex")]],
            combinators: vec![],
        };
    };
    let compounds = slice(&s.compounds, c.compounds)
        .iter()
        .map(|r| (r.lo..r.hi).map(|si| decode_simple(s, si)).collect())
        .collect();
    Cx {
        compounds,
        combinators: slice(&s.combinators, c.combinators).to_vec(),
    }
}

fn decode_list(s: &ExecSelectors, li: usize) -> Vec<Cx> {
    let Some(r) = s.lists.get(li).copied() else {
        return vec![Cx {
            compounds: vec![vec![broken("list")]],
            combinators: vec![],
        }];
    };
    // An argument's list is finished before the list that holds it.
    (r.lo..r.hi).map(|ci| decode_complex(s, ci)).collect()
}

/// The parse of `input` as a tree: the last list of the arrays is the result.
fn parse(input: &str) -> Option<Vec<Cx>> {
    let cps: Vec<u32> = input.chars().map(u32::from).collect();
    let s = parse_selector(&cps)?;
    // The result is the last list; an empty `lists` decodes as the out-of-bounds marker.
    Some(decode_list(&s, s.lists.len().saturating_sub(1)))
}

// Constructors, so that an expected tree reads like the selector.

fn ty(n: &str) -> S {
    S::Type(NsPrefix::Absent, n.to_owned())
}
fn tyns(ns: NsPrefix, n: &str) -> S {
    S::Type(ns, n.to_owned())
}
fn uni() -> S {
    S::Universal(NsPrefix::Absent)
}
fn id(n: &str) -> S {
    S::Id(n.to_owned())
}
fn cl(n: &str) -> S {
    S::Class(n.to_owned())
}
fn at(n: &str) -> S {
    S::Attr(NsPrefix::Absent, n.to_owned(), None)
}
fn atv(n: &str, m: AttrMatcher, v: &str, f: Option<CaseFlag>) -> S {
    S::Attr(NsPrefix::Absent, n.to_owned(), Some((m, v.to_owned(), f)))
}
fn cx(compounds: Vec<Vec<S>>, combinators: Vec<Combinator>) -> Cx {
    Cx {
        compounds,
        combinators,
    }
}
/// A complex selector of one compound selector.
fn one(compound: Vec<S>) -> Cx {
    cx(vec![compound], vec![])
}

/// Runs `(input, expected)` cases, expected `None` for "must be rejected".
fn check(cases: Vec<(&str, Option<Vec<Cx>>)>) {
    let mut wrong: Vec<String> = Vec::new();
    for (input, expected) in cases {
        let got = parse(input);
        if got != expected {
            wrong.push(format!(
                "{input:?}\n   got      {got:?}\n   expected {expected:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

use AttrMatcher::{DashMatch, Equals, Includes, Prefix, Substring, Suffix};
use Combinator::{Child, Descendant, NextSibling, SubsequentSibling};
use NsPrefix::{Any, NoNamespace};

// ------------------------------------------------------------------------------------
// §18 <complex-selector>, <combinator>, <selector-list>
// ------------------------------------------------------------------------------------

#[test]
fn combinators_and_their_order() {
    // §18: <complex-selector> = <compound-selector> [ <combinator>? <compound-selector> ]*,
    // <combinator> = '>' | '+' | '~'; "white space" alone is the descendant combinator (§16.1).
    check(vec![
        (
            "a b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a   b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a\n\t b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a > b",
            Some(vec![cx(vec![vec![ty("a")], vec![ty("b")]], vec![Child])]),
        ),
        (
            "a>b",
            Some(vec![cx(vec![vec![ty("a")], vec![ty("b")]], vec![Child])]),
        ),
        (
            "a >b",
            Some(vec![cx(vec![vec![ty("a")], vec![ty("b")]], vec![Child])]),
        ),
        (
            "a+b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![NextSibling],
            )]),
        ),
        (
            "a ~ b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![SubsequentSibling],
            )]),
        ),
        // The combinators are kept in source order, one between each two compounds.
        (
            "a b > c + d ~ e",
            Some(vec![cx(
                vec![
                    vec![ty("a")],
                    vec![ty("b")],
                    vec![ty("c")],
                    vec![ty("d")],
                    vec![ty("e")],
                ],
                vec![Descendant, Child, NextSibling, SubsequentSibling],
            )]),
        ),
        (
            "a ~ b + c > d e",
            Some(vec![cx(
                vec![
                    vec![ty("a")],
                    vec![ty("b")],
                    vec![ty("c")],
                    vec![ty("d")],
                    vec![ty("e")],
                ],
                vec![SubsequentSibling, NextSibling, Child, Descendant],
            )]),
        ),
        // Leading and trailing white space is not a combinator (§18: the string is trimmed
        // by "parse a selector"; CSS Syntax §5.4.1 strips it).
        (" a ", Some(vec![one(vec![ty("a")])])),
        ("\ta\n", Some(vec![one(vec![ty("a")])])),
    ]);
}

#[test]
fn selector_lists() {
    // §18: <selector-list> = <complex-selector-list>, comma-separated, one or more.
    check(vec![
        ("a, b", Some(vec![one(vec![ty("a")]), one(vec![ty("b")])])),
        ("a,b", Some(vec![one(vec![ty("a")]), one(vec![ty("b")])])),
        (
            " a , b ",
            Some(vec![one(vec![ty("a")]), one(vec![ty("b")])]),
        ),
        (
            "a b, c > d, e",
            Some(vec![
                cx(vec![vec![ty("a")], vec![ty("b")]], vec![Descendant]),
                cx(vec![vec![ty("c")], vec![ty("d")]], vec![Child]),
                one(vec![ty("e")]),
            ]),
        ),
    ]);
}

#[test]
fn grammar_errors_are_rejected() {
    // §18's `!` and `#` multipliers: each complex selector needs a compound selector on both
    // sides of a combinator, and each comma-separated item must be present; §3.10: "an empty
    // selector ... is invalid". An empty list is not a selector.
    check(vec![
        ("a > > b", None),
        ("a >> b", None),
        ("a > + b", None),
        ("> a", None),
        ("+ a", None),
        ("~ a", None),
        ("a >", None),
        ("a +", None),
        ("a ~", None),
        ("a,", None),
        (",a", None),
        ("a,,b", None),
        ("a, ,b", None),
        (",", None),
        ("", None),
        (" ", None),
        ("\n\t", None),
        ("a b,", None),
        ("a b, ", None),
        ("a, b,", None),
        // §18 lists `||` (the column combinator), which this UA has no usable support for:
        // invalid by §3.10. `!` is no token of the grammar.
        ("a || b", None),
        ("a ! b", None),
        // Two type selectors with nothing between them are not a compound selector (§18:
        // a compound's type selector is first), and no combinator joins them.
        ("a/**/b", None),
    ]);
}

// ------------------------------------------------------------------------------------
// §18 <type-selector>, <wq-name>, <ns-prefix>, §5
// ------------------------------------------------------------------------------------

#[test]
fn type_and_universal_selectors_with_namespaces() {
    check(vec![
        ("E", Some(vec![one(vec![ty("E")])])),
        ("*", Some(vec![one(vec![uni()])])),
        // §5.3: `*|E` "in any namespace", `|E` "without a namespace".
        ("*|E", Some(vec![one(vec![tyns(Any, "E")])])),
        ("|E", Some(vec![one(vec![tyns(NoNamespace, "E")])])),
        ("*|*", Some(vec![one(vec![S::Universal(Any)])])),
        ("|*", Some(vec![one(vec![S::Universal(NoNamespace)])])),
        // §5.3: "No white space is allowed between the namespace prefix, the `|` and the
        // name", so `* |a` is `*`, descendant, `|a`.
        (
            "* |a",
            Some(vec![cx(
                vec![vec![uni()], vec![tyns(NoNamespace, "a")]],
                vec![Descendant],
            )]),
        ),
        ("*| a", None),
        ("* | a", None),
        ("*|", None),
        ("|", None),
        ("a|", None),
        // §3.9 and §5.3: a selector whose prefix is not declared (no `@namespace` here, so
        // no prefix is) is invalid; spec.rs's modelling choice.
        ("ns|E", None),
        ("ns|*", None),
        ("a|b", None),
        // `|` is in the tail of a compound, not only at its head.
        ("a|b.c", None),
        // A type selector must come first in a compound (§18 <compound-selector>).
        (
            ".a b",
            Some(vec![cx(
                vec![vec![cl("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (".a*", None),
        (
            "#a b",
            Some(vec![cx(
                vec![vec![id("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        // `*` with simple selectors after it.
        ("*.a", Some(vec![one(vec![uni(), cl("a")])])),
        ("*|*.a", Some(vec![one(vec![S::Universal(Any), cl("a")])])),
        (
            "|a.b",
            Some(vec![one(vec![tyns(NoNamespace, "a"), cl("b")])]),
        ),
    ]);
}

#[test]
fn names_with_escapes_and_non_ascii() {
    check(vec![
        // CSS Syntax §4.3.7 "consume an escaped code point": `\31 ` is U+0031 and the space
        // ends the escape, so the identifier is "123".
        (".\\31 23", Some(vec![one(vec![cl("123")])])),
        // `\#` is the character itself.
        (".a\\#b", Some(vec![one(vec![cl("a#b")])])),
        ("\\#a", Some(vec![one(vec![ty("#a")])])),
        // Six hex digits, whitespace after is consumed: U+0041 is A.
        (".\\000041 b", Some(vec![one(vec![cl("Ab")])])),
        // A hash token's value, §4.3.4 `#` and "consume an ident sequence": `#a\62 c` is "abc".
        ("#a\\62 c", Some(vec![one(vec![id("abc")])])),
        // §4.2: U+00E9 and CJK are ident code points, so they are ident, not delimiters.
        ("\u{e9}", Some(vec![one(vec![ty("\u{e9}")])])),
        (
            ".\u{65e5}\u{672c}",
            Some(vec![one(vec![cl("\u{65e5}\u{672c}")])]),
        ),
        ("#\u{f1}x", Some(vec![one(vec![id("\u{f1}x")])])),
        // U+1F600, past U+FFFF, is "greater than or equal to U+10000": an ident code point.
        (".\u{1f600}", Some(vec![one(vec![cl("\u{1f600}")])])),
        ("[\u{e9}]", Some(vec![one(vec![at("\u{e9}")])])),
        // A leading `-` and `_` start an identifier.
        (".-x", Some(vec![one(vec![cl("-x")])])),
        ("._x", Some(vec![one(vec![cl("_x")])])),
        ("--x", Some(vec![one(vec![ty("--x")])])),
        // An escaped digit may start an identifier.
        ("\\31 a", Some(vec![one(vec![ty("1a")])])),
        // Names are kept as written; case is not folded at parse time.
        (
            "DiV.Foo#Bar",
            Some(vec![one(vec![ty("DiV"), cl("Foo"), id("Bar")])]),
        ),
    ]);
}

// ------------------------------------------------------------------------------------
// §18 <id-selector>, <class-selector>, <subclass-selector>
// ------------------------------------------------------------------------------------

#[test]
fn id_and_class_selectors() {
    check(vec![
        ("#a", Some(vec![one(vec![id("a")])])),
        (".a", Some(vec![one(vec![cl("a")])])),
        ("a.b.c", Some(vec![one(vec![ty("a"), cl("b"), cl("c")])])),
        ("a#b#c", Some(vec![one(vec![ty("a"), id("b"), id("c")])])),
        // Source order is kept within a compound selector.
        (
            ".a#b[c]:hover.d",
            Some(vec![one(vec![
                cl("a"),
                id("b"),
                at("c"),
                S::Pc(PseudoClass::Hover),
                cl("d"),
            ])]),
        ),
        // §18 <id-selector> = <hash-token>, which must be of type "id": `#1` is "unrestricted".
        ("#1", None),
        ("#-1", None),
        ("#", None),
        // §18 <class-selector> = '.' <ident-token>, no white space between.
        (".", None),
        (".1", None),
        (". a", None),
        (".a.", None),
        ("..a", None),
    ]);
}

// ------------------------------------------------------------------------------------
// §18 <attribute-selector>, <attr-matcher>, <attr-modifier>, §6
// ------------------------------------------------------------------------------------

#[test]
fn attribute_selectors() {
    use CaseFlag::{I, S as Sens};
    check(vec![
        ("[a]", Some(vec![one(vec![at("a")])])),
        ("[ a ]", Some(vec![one(vec![at("a")])])),
        ("[a=b]", Some(vec![one(vec![atv("a", Equals, "b", None)])])),
        (
            "[a~=b]",
            Some(vec![one(vec![atv("a", Includes, "b", None)])]),
        ),
        (
            "[a|=b]",
            Some(vec![one(vec![atv("a", DashMatch, "b", None)])]),
        ),
        ("[a^=b]", Some(vec![one(vec![atv("a", Prefix, "b", None)])])),
        ("[a$=b]", Some(vec![one(vec![atv("a", Suffix, "b", None)])])),
        (
            "[a*=b]",
            Some(vec![one(vec![atv("a", Substring, "b", None)])]),
        ),
        // The value is an ident or a string; quotes are not part of it.
        (
            "[a=\"b c\"]",
            Some(vec![one(vec![atv("a", Equals, "b c", None)])]),
        ),
        (
            "[a='b c']",
            Some(vec![one(vec![atv("a", Equals, "b c", None)])]),
        ),
        (
            "[a=\"\"]",
            Some(vec![one(vec![atv("a", Equals, "", None)])]),
        ),
        (
            "[a=\"1\"]",
            Some(vec![one(vec![atv("a", Equals, "1", None)])]),
        ),
        // CSS Syntax §4.3.5: escapes in a string, `\41 ` is A, and a backslash-newline is
        // dropped.
        (
            "[a=\"\\41 b\"]",
            Some(vec![one(vec![atv("a", Equals, "Ab", None)])]),
        ),
        (
            "[a=\"x\\\ny\"]",
            Some(vec![one(vec![atv("a", Equals, "xy", None)])]),
        ),
        // White space around each part is allowed (§18's `<wq-name>` `<attr-matcher>` value).
        (
            "[ a = b ]",
            Some(vec![one(vec![atv("a", Equals, "b", None)])]),
        ),
        (
            "[a\t~=\nb]",
            Some(vec![one(vec![atv("a", Includes, "b", None)])]),
        ),
        // §6.3 flags `i` and `s`; keywords are ASCII case-insensitive (CSS Values §2.1).
        (
            "[a=b i]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(I))])]),
        ),
        (
            "[a=b s]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(Sens))])]),
        ),
        (
            "[a=b I]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(I))])]),
        ),
        (
            "[a=b S]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(Sens))])]),
        ),
        (
            "[a=\"b\" i]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(I))])]),
        ),
        (
            "[a=\"b\"i]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(I))])]),
        ),
        (
            "[a*=\"b\" s ]",
            Some(vec![one(vec![atv("a", Substring, "b", Some(Sens))])]),
        ),
        // §6.4 namespace components of the attribute name.
        (
            "[*|a]",
            Some(vec![one(vec![S::Attr(Any, "a".into(), None)])]),
        ),
        (
            "[|a]",
            Some(vec![one(vec![S::Attr(NoNamespace, "a".into(), None)])]),
        ),
        (
            "[*|a=b]",
            Some(vec![one(vec![S::Attr(
                Any,
                "a".into(),
                Some((Equals, "b".into(), None)),
            )])]),
        ),
        (
            "[|a|=b]",
            Some(vec![one(vec![S::Attr(
                NoNamespace,
                "a".into(),
                Some((DashMatch, "b".into(), None)),
            )])]),
        ),
        // A named prefix is undeclared (spec.rs's modelling choice, §3.9).
        ("[ns|a]", None),
        ("[ns|a=b]", None),
        // Escapes in the name.
        (
            "[\\61 =b]",
            Some(vec![one(vec![atv("a", Equals, "b", None)])]),
        ),
        // Several attribute selectors, in order.
        (
            "a[b][c=d]",
            Some(vec![one(vec![
                ty("a"),
                at("b"),
                atv("c", Equals, "d", None),
            ])]),
        ),
        // Invalid: §18's <attribute-selector> = '[' <wq-name> ']' | '[' <wq-name>
        // <attr-matcher> [ <string-token> | <ident-token> ] <attr-modifier>? ']'.
        ("[]", None),
        ("[ ]", None),
        ("[=a]", None),
        ("[a=]", None),
        ("[a=1]", None),
        ("[a=b c]", None),
        ("[a=b j]", None),
        ("[a=b i i]", None),
        ("[a=b i s]", None),
        ("[a b]", None),
        ("[a==b]", None),
        ("[a!=b]", None),
        ("[a=\"b\" \"c\"]", None),
        ("[a i]", None),
        ("[1]", None),
    ]);
    // An unclosed block is closed at EOF (CSS Syntax §5.4.7 "consume a simple block").
    check(vec![(
        "[a=b",
        Some(vec![one(vec![atv("a", Equals, "b", None)])]),
    )]);
}

// ------------------------------------------------------------------------------------
// §18 <pseudo-class-selector>, <pseudo-element-selector>, §9, §11, §15
// ------------------------------------------------------------------------------------

#[test]
fn pseudo_classes_by_name_and_case() {
    use PseudoClass as P;
    let names: &[(&str, PseudoClass)] = &[
        ("link", P::Link),
        ("visited", P::Visited),
        ("any-link", P::AnyLink),
        ("root", P::Root),
        ("empty", P::Empty),
        ("first-child", P::FirstChild),
        ("last-child", P::LastChild),
        ("only-child", P::OnlyChild),
        ("first-of-type", P::FirstOfType),
        ("last-of-type", P::LastOfType),
        ("only-of-type", P::OnlyOfType),
        ("hover", P::Hover),
        ("active", P::Active),
        ("focus", P::Focus),
        ("focus-visible", P::FocusVisible),
        ("focus-within", P::FocusWithin),
    ];
    let mut cases: Vec<(String, Option<Vec<Cx>>)> = Vec::new();
    for (n, class) in names {
        cases.push((format!(":{n}"), Some(vec![one(vec![S::Pc(*class)])])));
        // CSS keywords, and so pseudo-class names, are ASCII case-insensitive.
        cases.push((
            format!(":{}", n.to_uppercase()),
            Some(vec![one(vec![S::Pc(*class)])]),
        ));
        cases.push((
            format!("a:{n}"),
            Some(vec![one(vec![ty("a"), S::Pc(*class)])]),
        ));
    }
    cases.push((
        ":FiRsT-Child".to_owned(),
        Some(vec![one(vec![S::Pc(P::FirstChild)])]),
    ));
    // Not in the subset: invalid (§3.10), and an argument where there is none.
    for bad in [
        ":foo",
        ":checked",
        ":lang(en)",
        ":hover(x)",
        ":link()",
        ":root(a)",
        ":",
        "a:",
        ": hover",
        ":has(a)",
        ":host",
        ":-moz-x",
        ":first-child(2)",
        ":nth-child",
        ":is",
        ":not",
    ] {
        cases.push((bad.to_owned(), None));
    }
    let borrowed: Vec<(&str, Option<Vec<Cx>>)> =
        cases.iter().map(|(s, e)| (s.as_str(), e.clone())).collect();
    check(borrowed);
}

#[test]
fn pseudo_elements_in_both_spellings() {
    use PseudoClass::{Focus, Hover};
    use PseudoElement::{After, Before, FirstLetter, FirstLine};
    let pe = S::Pe;
    check(vec![
        // §3.6: `::name`; and "for compatibility with existing style sheets" CSS2's single
        // colon form of :before, :after, :first-line and :first-letter (§3.6.1's note).
        ("::before", Some(vec![one(vec![pe(Before)])])),
        ("::after", Some(vec![one(vec![pe(After)])])),
        ("::first-line", Some(vec![one(vec![pe(FirstLine)])])),
        ("::first-letter", Some(vec![one(vec![pe(FirstLetter)])])),
        (":before", Some(vec![one(vec![pe(Before)])])),
        (":after", Some(vec![one(vec![pe(After)])])),
        (":first-line", Some(vec![one(vec![pe(FirstLine)])])),
        (":first-letter", Some(vec![one(vec![pe(FirstLetter)])])),
        // Names are ASCII case-insensitive.
        ("::BEFORE", Some(vec![one(vec![pe(Before)])])),
        (":After", Some(vec![one(vec![pe(After)])])),
        ("a::before", Some(vec![one(vec![ty("a"), pe(Before)])])),
        ("a:before", Some(vec![one(vec![ty("a"), pe(Before)])])),
        (
            ".x#y::first-line",
            Some(vec![one(vec![cl("x"), id("y"), pe(FirstLine)])]),
        ),
        // §3.6 / §18's note: only the user action pseudo-classes may follow one, in order.
        (
            "a::before:hover",
            Some(vec![one(vec![ty("a"), pe(Before), S::Pc(Hover)])]),
        ),
        (
            "a::after:hover:focus",
            Some(vec![one(vec![
                ty("a"),
                pe(After),
                S::Pc(Hover),
                S::Pc(Focus),
            ])]),
        ),
        ("a::before:first-child", None),
        ("a::before.b", None),
        ("a::before#b", None),
        ("a::before[b]", None),
        ("a::before::after", None),
        ("a::before:before", None),
        // At the end of the selector only: nothing combines after it.
        ("a::before b", None),
        ("a::before > b", None),
        ("a::before + b", None),
        // But another item of a list may follow.
        (
            "a::before, b",
            Some(vec![one(vec![ty("a"), pe(Before)]), one(vec![ty("b")])]),
        ),
        // A pseudo-element may end a later compound.
        (
            "a b::after",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b"), pe(After)]],
                vec![Descendant],
            )]),
        ),
        // Not in the subset (no functional pseudo-elements either).
        ("::foo", None),
        ("::selection", None),
        ("::before(x)", None),
        ("::", None),
        (":::before", None),
        ("a::", None),
    ]);
}

#[test]
fn is_where_and_not() {
    use PseudoClass::Hover;
    check(vec![
        // §4.2/§4.4: :is() and :where() take a <forgiving-selector-list>; §4.3 :not() a
        // <complex-real-selector-list>.
        (
            ":is(a)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":is(a, b)",
            Some(vec![one(vec![S::Is(vec![
                one(vec![ty("a")]),
                one(vec![ty("b")]),
            ])])]),
        ),
        (
            ":where(a, .b)",
            Some(vec![one(vec![S::Where(vec![
                one(vec![ty("a")]),
                one(vec![cl("b")]),
            ])])]),
        ),
        (
            ":not(a, .b)",
            Some(vec![one(vec![S::Not(vec![
                one(vec![ty("a")]),
                one(vec![cl("b")]),
            ])])]),
        ),
        // Function names are ASCII case-insensitive.
        (
            ":IS(a)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":Where(a)",
            Some(vec![one(vec![S::Where(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":NOT(a)",
            Some(vec![one(vec![S::Not(vec![one(vec![ty("a")])])])]),
        ),
        // Complex arguments, with combinators.
        (
            ":not(a > b)",
            Some(vec![one(vec![S::Not(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Child],
            )])])]),
        ),
        (
            ":is(a b, c + d)",
            Some(vec![one(vec![S::Is(vec![
                cx(vec![vec![ty("a")], vec![ty("b")]], vec![Descendant]),
                cx(vec![vec![ty("c")], vec![ty("d")]], vec![NextSibling]),
            ])])]),
        ),
        // Whitespace inside the parentheses.
        (
            ":is( a , b )",
            Some(vec![one(vec![S::Is(vec![
                one(vec![ty("a")]),
                one(vec![ty("b")]),
            ])])]),
        ),
        // Nesting.
        (
            ":is(:is(a), :not(.b))",
            Some(vec![one(vec![S::Is(vec![
                one(vec![S::Is(vec![one(vec![ty("a")])])]),
                one(vec![S::Not(vec![one(vec![cl("b")])])]),
            ])])]),
        ),
        (
            ":not(:where(a:hover))",
            Some(vec![one(vec![S::Not(vec![one(vec![S::Where(vec![
                one(vec![ty("a"), S::Pc(Hover)]),
            ])])])])]),
        ),
        // In a compound with other simple selectors, in order.
        (
            "a:not(.b):is(c)",
            Some(vec![one(vec![
                ty("a"),
                S::Not(vec![one(vec![cl("b")])]),
                S::Is(vec![one(vec![ty("c")])]),
            ])]),
        ),
        // §18.1 forgiving selector list: an empty argument is valid and empty, an empty or
        // invalid item is dropped, the rest kept.
        (":is()", Some(vec![one(vec![S::Is(vec![])])])),
        (":where()", Some(vec![one(vec![S::Where(vec![])])])),
        (":is( )", Some(vec![one(vec![S::Is(vec![])])])),
        (":is(,)", Some(vec![one(vec![S::Is(vec![])])])),
        (
            ":is(a,)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":is(,a)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":is(a,,b)",
            Some(vec![one(vec![S::Is(vec![
                one(vec![ty("a")]),
                one(vec![ty("b")]),
            ])])]),
        ),
        (":is(1)", Some(vec![one(vec![S::Is(vec![])])])),
        (
            ":is(a, 1, b)",
            Some(vec![one(vec![S::Is(vec![
                one(vec![ty("a")]),
                one(vec![ty("b")]),
            ])])]),
        ),
        (
            ":where(a b c d, :foo)",
            Some(vec![one(vec![S::Where(vec![cx(
                vec![vec![ty("a")], vec![ty("b")], vec![ty("c")], vec![ty("d")]],
                vec![Descendant, Descendant, Descendant],
            )])])]),
        ),
        // A pseudo-element is not valid in :is()/:where() (§4.2): the item is dropped; and in
        // :not() the whole selector is invalid (§4.3).
        (":is(::before)", Some(vec![one(vec![S::Is(vec![])])])),
        (
            ":is(a, ::before)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (":not(::before)", None),
        (":not(a::before)", None),
        // :not() is not forgiving: empty, or an empty or invalid item, is invalid.
        (":not()", None),
        (":not( )", None),
        (":not(,)", None),
        (":not(a,)", None),
        (":not(,a)", None),
        (":not(a,,b)", None),
        (":not(1)", None),
        (":not(a, 1)", None),
        // Unclosed: a function block is closed at EOF (CSS Syntax §5.4.7).
        (
            ":is(a",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
    ]);
}

// ------------------------------------------------------------------------------------
// <an+b> (CSS Syntax §6.2) in the four :nth-* pseudo-classes
// ------------------------------------------------------------------------------------

#[test]
fn nth_pseudo_classes_and_their_an_plus_b() {
    use NthKind::{Child, LastChild, LastOfType, OfType};
    // (argument, A, B), from CSS Syntax §6.2's productions: odd = 2n+1, even = 2n.
    let ok: &[(&str, i32, i32)] = &[
        ("odd", 2, 1),
        ("even", 2, 0),
        ("ODD", 2, 1),
        ("Even", 2, 0),
        ("2n+1", 2, 1),
        ("2n + 1", 2, 1),
        ("2n+ 1", 2, 1),
        ("2n +1", 2, 1),
        ("2n-1", 2, -1),
        ("2n - 1", 2, -1),
        ("2N+1", 2, 1),
        ("-2n+5", -2, 5),
        ("-2n - 5", -2, -5),
        ("+3n", 3, 0),
        ("3n", 3, 0),
        ("-3n", -3, 0),
        ("0n+0", 0, 0),
        ("0n+5", 0, 5),
        ("-0n+5", 0, 5),
        ("n", 1, 0),
        ("+n", 1, 0),
        ("-n", -1, 0),
        ("N", 1, 0),
        ("n+3", 1, 3),
        ("+n+3", 1, 3),
        ("-n+3", -1, 3),
        ("n-3", 1, -3),
        ("+n-3", 1, -3),
        ("-n-3", -1, -3),
        ("n- 3", 1, -3),
        ("-n- 3", -1, -3),
        ("n +3", 1, 3),
        ("n + 3", 1, 3),
        ("n - 3", 1, -3),
        ("-n + 3", -1, 3),
        // A bare integer is B with A = 0.
        ("3", 0, 3),
        ("0", 0, 0),
        ("+5", 0, 5),
        ("-3", 0, -3),
        ("007", 0, 7),
        (" 3 ", 0, 3),
        ("\n2n\t+\n1 ", 2, 1),
        // A large step.
        ("10n+10", 10, 10),
        ("1n+1", 1, 1),
        // Clamping to the 32-bit signed range (spec.rs's modelling choice, CSS Values 4
        // §5.1): at the limit and past it, on A, on B and on a bare integer.
        ("2147483647n+2147483647", i32::MAX, i32::MAX),
        ("2147483646n+2147483646", 2_147_483_646, 2_147_483_646),
        ("2147483648n+2147483648", i32::MAX, i32::MAX),
        ("99999999999n+99999999999", i32::MAX, i32::MAX),
        ("-2147483647n-2147483647", -2_147_483_647, -2_147_483_647),
        ("-2147483648n-2147483648", i32::MIN, i32::MIN),
        ("-2147483649n-2147483649", i32::MIN, i32::MIN),
        ("-99999999999n-99999999999", i32::MIN, i32::MIN),
        ("2147483647", 0, i32::MAX),
        ("2147483648", 0, i32::MAX),
        ("-2147483647", 0, -2_147_483_647),
        ("-2147483648", 0, i32::MIN),
        ("-2147483649", 0, i32::MIN),
        ("n-2147483649", 1, i32::MIN),
        ("n+2147483649", 1, i32::MAX),
        ("-n-99999999999", -1, i32::MIN),
        ("2n-99999999999", 2, i32::MIN),
        // A very long digit string still clamps rather than wrapping.
        ("99999999999999999999999999999999999999999999n", i32::MAX, 0),
        (
            "n-99999999999999999999999999999999999999999999",
            1,
            i32::MIN,
        ),
        ("-99999999999999999999999999999999999999999999", 0, i32::MIN),
    ];
    let bad: &[&str] = &[
        "",
        " ",
        "n+",
        "n-",
        "2n+",
        "+ n",
        "+ 3",
        "2 n",
        "2n 1",
        "2n+-1",
        "2n--1",
        "2n++1",
        "n+ -1",
        "n+1.5",
        "1.5",
        "1.5n",
        "1e1",
        "2n+1n",
        "-",
        "+",
        "- n",
        "n n",
        "odd+1",
        "even-1",
        "oddd",
        "evens",
        "3 3",
        "n+1 2",
        "2n+1 of a",
        "2n+1 of",
        "of a",
        "a",
        "2n+a",
        "--n",
        "+-n",
        "n-+1",
        "2n+ +1",
        "2n -+1",
        "+n-",
        "- 3",
        "2n+1,3",
        "2n 3",
        "n n+1",
        "3n+",
        "\"3\"",
        "#3",
        "(3)",
        "n- -3",
        "n-b1",
        "2n - - 1",
    ];
    let kinds = [
        ("nth-child", Child),
        ("nth-last-child", LastChild),
        ("nth-of-type", OfType),
        ("nth-last-of-type", LastOfType),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (fname, kind) in kinds {
        for (arg, a, b) in ok {
            let input = format!(":{fname}({arg})");
            let want = Some(vec![one(vec![S::Nth(kind, *a, *b)])]);
            let got = parse(&input);
            if got != want {
                wrong.push(format!("{input:?}: got {got:?}, expected {want:?}"));
            }
        }
        for arg in bad {
            let input = format!(":{fname}({arg})");
            if let Some(got) = parse(&input) {
                wrong.push(format!("{input:?}: accepted as {got:?}"));
            }
        }
        // The name is ASCII case-insensitive; the argument may be empty only if invalid.
        let upper = format!(":{}(2n+1)", fname.to_uppercase());
        let want = Some(vec![one(vec![S::Nth(kind, 2, 1)])]);
        if parse(&upper) != want {
            wrong.push(format!("{upper:?}: expected {want:?}"));
        }
        let empty = format!(":{fname}()");
        if parse(&empty).is_some() {
            wrong.push(format!("{empty:?}: accepted"));
        }
    }
    // The pseudo-class stands with other simple selectors.
    let got = parse("li:nth-child(2n+1).x");
    let want = Some(vec![one(vec![ty("li"), S::Nth(Child, 2, 1), cl("x")])]);
    if got != want {
        wrong.push(format!("compound: got {got:?}"));
    }
    // :nth-child takes no more than <an+b> here: `of S` is not in the subset (invalid).
    for input in [
        ":nth-child(2n+1 of a)",
        ":nth-last-child(1 of .x)",
        ":nth-child",
    ] {
        if parse(input).is_some() {
            wrong.push(format!("{input:?}: accepted"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

// ------------------------------------------------------------------------------------
// Comments (CSS Syntax §4.3.2: "consume comments" drops them before the grammar)
// ------------------------------------------------------------------------------------

#[test]
fn comments_between_tokens() {
    check(vec![
        ("/**/a", Some(vec![one(vec![ty("a")])])),
        ("a/**/", Some(vec![one(vec![ty("a")])])),
        ("/* x */ a /* y */", Some(vec![one(vec![ty("a")])])),
        // A comment is not white space: no descendant combinator, and a compound continues
        // across it.
        ("a/**/.b", Some(vec![one(vec![ty("a"), cl("b")])])),
        ("a/**/#b", Some(vec![one(vec![ty("a"), id("b")])])),
        (
            "a/**/:hover",
            Some(vec![one(vec![ty("a"), S::Pc(PseudoClass::Hover)])]),
        ),
        ("a/**/b", None),
        // White space around a comment is white space.
        (
            "a /**/ b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a/**/ b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a /**/b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![Descendant],
            )]),
        ),
        (
            "a/**/>/**/b",
            Some(vec![cx(vec![vec![ty("a")], vec![ty("b")]], vec![Child])]),
        ),
        (
            "a/**/+/**/b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![NextSibling],
            )]),
        ),
        (
            "a/* , */~/* > */b",
            Some(vec![cx(
                vec![vec![ty("a")], vec![ty("b")]],
                vec![SubsequentSibling],
            )]),
        ),
        (
            "a,/**/b",
            Some(vec![one(vec![ty("a")]), one(vec![ty("b")])]),
        ),
        (
            "a/**/,b",
            Some(vec![one(vec![ty("a")]), one(vec![ty("b")])]),
        ),
        // A comment hides what is inside it.
        ("a/* , b */", Some(vec![one(vec![ty("a")])])),
        ("/* a */", None),
        ("a,/**/", None),
        // Inside brackets and arguments.
        (
            "[/**/a/**/=/**/b/**/]",
            Some(vec![one(vec![atv("a", Equals, "b", None)])]),
        ),
        (
            "[a=b/**/i]",
            Some(vec![one(vec![atv("a", Equals, "b", Some(CaseFlag::I))])]),
        ),
        (
            ":is(/**/a/**/)",
            Some(vec![one(vec![S::Is(vec![one(vec![ty("a")])])])]),
        ),
        (
            ":nth-child(/**/2n/**/+/**/1/**/)",
            Some(vec![one(vec![S::Nth(NthKind::Child, 2, 1)])]),
        ),
        // A comment is not white space, and the tokenizer drops it, so what is left is `*|a`
        // (§5.3's ban is on white space between the parts).
        ("*/**/|a", Some(vec![one(vec![tyns(Any, "a")])])),
        ("*|/**/a", Some(vec![one(vec![tyns(Any, "a")])])),
        // An unclosed comment runs to the end.
        ("a/* b", Some(vec![one(vec![ty("a")])])),
    ]);
}

// ------------------------------------------------------------------------------------
// The result is in the arrays' own terms too
// ------------------------------------------------------------------------------------

#[test]
fn argument_lists_come_before_the_list_that_holds_them() {
    // exec_types.rs: "an argument's list always has a smaller index". The decoder relies on
    // it only through `lists.last()` being the result.
    let cps: Vec<u32> = ":is(a, :not(b)) c".chars().map(u32::from).collect();
    let parsed = parse_selector(&cps);
    assert!(parsed.is_some(), "the selector is valid");
    let Some(s) = parsed else {
        return;
    };
    for simple in &s.simples {
        if let ExecSimple::Is { list } | ExecSimple::Where { list } | ExecSimple::Not { list } =
            simple
        {
            assert!(
                list.saturating_add(1) < s.lists.len(),
                "argument list {list} not before the result"
            );
        }
    }
    let got = decode_list(&s, s.lists.len().saturating_sub(1));
    let want = vec![cx(
        vec![
            vec![S::Is(vec![
                one(vec![ty("a")]),
                one(vec![S::Not(vec![one(vec![ty("b")])])]),
            ])],
            vec![ty("c")],
        ],
        vec![Descendant],
    )];
    assert_eq!(got, want);
}
