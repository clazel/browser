//! Specificity (Selectors Level 4 §17) through the parser: pseudo-elements, `:nth-*()`,
//! `:is()`, `:not()` and `:where()` with lists and nesting, the specificity of each selector
//! of a list (not only the maximum `list_specificity_of` gives), and sums through nesting.
//! (Saturation is not reachable from a test; see the last test.)
//!
//! §17: "count the number of ID selectors in the selector (= A); count the number of class
//! selectors, attributes selectors, and pseudo-classes in the selector (= B); count the
//! number of type selectors and pseudo-elements in the selector (= C); ignore the universal
//! selector". "The specificity of an :is(), :not(), or :has() pseudo-class is replaced by the
//! specificity of the most specific complex selector in its selector list argument." "The
//! specificity of a :where() pseudo-class is replaced by zero." ":nth-child() ... is the
//! specificity of the pseudo-class itself (counting as one pseudo-class selector) plus the
//! specificity of the most specific complex selector in its selector list argument (if any)":
//! this UA has no `of S`, so one pseudo-class. "Specificities are compared by comparing the
//! three components in order: ... A ... B ... C". Components saturate at `u32::MAX`
//! (spec.rs's modelling choice, from "values higher than the limit must be clamped to that
//! limit, and not overflow").

use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_specificity::{
    ExecSpecificity, complex_specificity_of, list_specificity_of,
};
use clazel_selectors::exec_types::{ExecComplex, ExecRange, ExecSelectors, ExecSimple};
use clazel_selectors::spec::{Combinator, NsPrefix};

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// (A, B, C).
type Triple = (u32, u32, u32);

/// A selector list, the specificity of each of its selectors, and the most specific.
type ListCase<'a> = (&'a str, &'a [Triple], Triple);

fn abc(a: u32, b: u32, c: u32) -> ExecSpecificity {
    ExecSpecificity { a, b, c }
}

/// The specificity of each complex selector of the result list of `selector`, and the
/// most specific of them.
fn specificities(selector: &str) -> Option<(Vec<ExecSpecificity>, ExecSpecificity)> {
    let s = parse_selector(&cps(selector))?;
    let last = s.lists.len().saturating_sub(1);
    let r = s.lists.get(last).copied()?;
    let each = (r.lo..r.hi)
        .map(|ci| complex_specificity_of(&s, last, ci))
        .collect();
    Some((each, list_specificity_of(&s, last)))
}

#[test]
fn pseudo_elements_nth_and_pseudo_classes() {
    let cases: &[(&str, (u32, u32, u32))] = &[
        // A pseudo-element counts as a type selector (C).
        ("::before", (0, 0, 1)),
        (":after", (0, 0, 1)),
        ("a::before", (0, 0, 2)),
        ("a b::first-line", (0, 0, 3)),
        // The user action pseudo-classes allowed after it are pseudo-classes (B).
        ("a::first-line:hover", (0, 1, 2)),
        ("::before:hover:focus", (0, 2, 1)),
        // `:nth-*()` without `of S` is one pseudo-class, whatever A and B are.
        (":nth-child(2n+1)", (0, 1, 0)),
        (":nth-last-child(-n+3)", (0, 1, 0)),
        ("li:nth-last-of-type(2)", (0, 1, 1)),
        ("li:nth-of-type(odd):first-child", (0, 2, 1)),
        (":first-child", (0, 1, 0)),
        (":root:empty", (0, 2, 0)),
        // Attribute selectors are B; namespace components and `*` count for nothing; a
        // repeated simple selector counts each time.
        ("[a]", (0, 1, 0)),
        ("[*|a=b i]", (0, 1, 0)),
        ("*|*", (0, 0, 0)),
        ("|a", (0, 0, 1)),
        ("*|a", (0, 0, 1)),
        ("#a#a", (2, 0, 0)),
        (".a.a", (0, 2, 0)),
        ("a a", (0, 0, 2)),
        ("a > b + c ~ d e", (0, 0, 5)),
        ("#a .b c", (1, 1, 1)),
    ];
    check(cases);
}

#[test]
fn is_not_where_with_lists_and_nesting() {
    let cases: &[(&str, (u32, u32, u32))] = &[
        // :is() and :not() take the most specific argument, compared A then B then C.
        (":is()", (0, 0, 0)),
        (":is(a)", (0, 0, 1)),
        (":is(a, #b, .c)", (1, 0, 0)),
        (":not(.a, #b)", (1, 0, 0)),
        (":not(a)", (0, 0, 1)),
        // A larger C does not beat a B, nor a larger B an A.
        (":is(a b c, .d)", (0, 1, 0)),
        (":is(#a, .b.c.d.e)", (1, 0, 0)),
        (":is(a b c d, e)", (0, 0, 4)),
        // The most specific is taken whole, not component-wise (it is not (1, 2, 3)).
        (":is(#a, .b.c, d e f)", (1, 0, 0)),
        (":not(a, .b, #c d)", (1, 0, 1)),
        (":is(.a b, .a c, .d)", (0, 1, 1)),
        // :where() is zero, with anything in it.
        (":where(#a)", (0, 0, 0)),
        (":where(#a, .b c) d", (0, 0, 1)),
        (":where()", (0, 0, 0)),
        (".a:where(#b#c, .d)", (0, 1, 0)),
        // Nesting: each level takes its own most specific.
        (":is(:where(#a), .b)", (0, 1, 0)),
        (":is(:is(#a), b)", (1, 0, 0)),
        (":not(:not(#a))", (1, 0, 0)),
        (":is(:not(.a, b), c)", (0, 1, 0)),
        (":not(:is(a b, :where(#c)))", (0, 0, 2)),
        // Alongside other simple selectors, the sum.
        ("a:not(:is(b c))", (0, 0, 3)),
        (":not(#a):not(#b)", (2, 0, 0)),
        ("a:is(#b)::before", (1, 0, 2)),
        (".a:is(.b, .c).d", (0, 3, 0)),
        // A pseudo-element is not valid inside :is() (spec.rs drops it), so it adds nothing.
        (":is(::before, .a)", (0, 1, 0)),
    ];
    check(cases);
}

fn check(cases: &[(&str, (u32, u32, u32))]) {
    let mut wrong: Vec<String> = Vec::new();
    for (selector, (a, b, c)) in cases {
        let Some((each, max)) = specificities(selector) else {
            wrong.push(format!("{selector:?} did not parse"));
            continue;
        };
        let want = abc(*a, *b, *c);
        // A single complex selector: it is the maximum too.
        if each != [want] || max != want {
            wrong.push(format!(
                "{selector:?}: {each:?} (max {max:?}), expected {want:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_selector_of_a_list_has_its_own_specificity() {
    // §17: "If the selector is a selector list, this number is calculated for each selector in
    // the list." The list's maximum (what :is() would take) is one of them.
    let cases: &[ListCase] = &[
        ("a, #b, .c.d", &[(0, 0, 1), (1, 0, 0), (0, 2, 0)], (1, 0, 0)),
        (
            "a, #b, .c.d, :is(#x, .y) z, ::before",
            &[(0, 0, 1), (1, 0, 0), (0, 2, 0), (1, 0, 1), (0, 0, 1)],
            (1, 0, 1),
        ),
        // The order of the list is the order of the results, and the maximum is not the
        // last, nor the first.
        (".a, #b, c", &[(0, 1, 0), (1, 0, 0), (0, 0, 1)], (1, 0, 0)),
        ("#b, .a, c", &[(1, 0, 0), (0, 1, 0), (0, 0, 1)], (1, 0, 0)),
        ("c, .a, #b", &[(0, 0, 1), (0, 1, 0), (1, 0, 0)], (1, 0, 0)),
        // Equal specificities, and ties broken by a lower component.
        ("a, b", &[(0, 0, 1), (0, 0, 1)], (0, 0, 1)),
        (".a b, .c", &[(0, 1, 1), (0, 1, 0)], (0, 1, 1)),
        ("*, a", &[(0, 0, 0), (0, 0, 1)], (0, 0, 1)),
        // A list inside a function does not change the outer list's items.
        (":is(#a, b), c", &[(1, 0, 0), (0, 0, 1)], (1, 0, 0)),
        (":where(#a), c", &[(0, 0, 0), (0, 0, 1)], (0, 0, 1)),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (selector, each, max) in cases {
        let Some((got_each, got_max)) = specificities(selector) else {
            wrong.push(format!("{selector:?} did not parse"));
            continue;
        };
        let want_each: Vec<ExecSpecificity> = each.iter().map(|&(a, b, c)| abc(a, b, c)).collect();
        let want_max = abc(max.0, max.1, max.2);
        if got_each != want_each || got_max != want_max {
            wrong.push(format!(
                "{selector:?}: {got_each:?} (max {got_max:?}), expected {want_each:?} (max {want_max:?})"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

// ------------------------------------------------------------------------------------
// Sums through nesting
// ------------------------------------------------------------------------------------

/// How a level adds up its two copies of the level below.
#[derive(Clone, Copy)]
enum Join {
    /// One compound selector of two simple selectors, each `:is()` of the level below.
    InOneCompound,
    /// Two compound selectors, each one `:is()` of the level below.
    InTwoCompounds,
}

/// Selectors that double at each level without being exponentially large in memory: level 0 is the
/// complex selector `#a.b c`, (1, 1, 1); list k holds one complex selector whose simple
/// selectors are two `:is()` of list k-1 (in one compound or in two). A level's
/// specificity is the sum of its two copies, 2^k times (1, 1, 1).
fn doubling(levels: usize, join: Join) -> ExecSelectors {
    let mut s = ExecSelectors {
        simples: vec![
            ExecSimple::Id { name: cps("a") },
            ExecSimple::Class { name: cps("b") },
            ExecSimple::Type {
                ns: NsPrefix::Absent,
                name: cps("c"),
            },
        ],
        compounds: vec![ExecRange { lo: 0, hi: 3 }],
        combinators: vec![],
        complexes: vec![ExecComplex {
            compounds: ExecRange { lo: 0, hi: 1 },
            combinators: ExecRange { lo: 0, hi: 0 },
        }],
        lists: vec![ExecRange { lo: 0, hi: 1 }],
    };
    for below in 0..levels {
        let first = s.simples.len();
        s.simples.push(ExecSimple::Is { list: below });
        s.simples.push(ExecSimple::Is { list: below });
        let c_lo = s.compounds.len();
        let k_lo = s.combinators.len();
        let second = first.saturating_add(1);
        match join {
            Join::InOneCompound => s.compounds.push(ExecRange {
                lo: first,
                hi: first.saturating_add(2),
            }),
            Join::InTwoCompounds => {
                s.compounds.push(ExecRange {
                    lo: first,
                    hi: second,
                });
                s.compounds.push(ExecRange {
                    lo: second,
                    hi: second.saturating_add(1),
                });
                s.combinators.push(Combinator::Descendant);
            }
        }
        let x_lo = s.complexes.len();
        s.complexes.push(ExecComplex {
            compounds: ExecRange {
                lo: c_lo,
                hi: s.compounds.len(),
            },
            combinators: ExecRange {
                lo: k_lo,
                hi: s.combinators.len(),
            },
        });
        s.lists.push(ExecRange {
            lo: x_lo,
            hi: x_lo.saturating_add(1),
        });
    }
    s
}

#[test]
fn deeply_nested_sums_are_exact_below_the_limit() {
    // Saturation itself cannot be reached from a test: a component only counts simple
    // selectors, and `exec_specificity` evaluates a list once per `:is()` that names it, so
    // 2^32 of them (here, level 32 of the doubling) is 2^32 evaluations. The parser never
    // shares a list, so its output is evaluated in time linear in its size. What this does
    // check is that the sums are exact on the way up (no early clamp, no overflow into the
    // next component). `saturating` in exec_specificity.rs is proven equal to the spec's
    // `saturate`, and the spec's is pinned by the mutation `saturate-limit`.
    for join in [Join::InOneCompound, Join::InTwoCompounds] {
        for k in 0..=18u32 {
            let s = doubling(k as usize, join);
            let last = s.lists.len().saturating_sub(1);
            let got = list_specificity_of(&s, last);
            // 2^k, below the limit for these k.
            let n = 2u32.saturating_pow(k);
            assert_eq!(got, abc(n, n, n), "level {k}");
            // The complex selector's own sum is the list's maximum, as it is the only one.
            let only = s.lists.get(last).map_or(0, |r| r.lo);
            assert_eq!(complex_specificity_of(&s, last, only), got);
        }
    }
}
