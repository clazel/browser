//! One step of each loop of the spec's grammar ([`super::spec`]), as lemmas, so that the
//! executable parser's proofs (in [`super::exec_parse`]) name the step they take and keep
//! their own queries small.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The next comma is between `i` and `hi`.
pub proof fn lemma_next_comma_bounds(l: Seq<ComponentValue>, i: int, hi: int)
    requires
        0 <= i <= hi <= l.len(),
    ensures
        i <= next_comma(l, i, hi) <= hi,
    decreases hi - i,
{
    if i < hi && is(l[i], Token::Comma) == false {
        lemma_next_comma_bounds(l, i + 1, hi);
    }
}

/// `compound_selector` read nothing, or failed: the complex selector fails.
pub proof fn lemma_cs_fails(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    ks: Seq<Combinator>,
    np: bool,
)
    requires
        compound_selector(l, i, hi, np) is None || (compound_selector(l, i, hi, np) is Some && ({
            let (cmp, next) = compound_selector(l, i, hi, np).unwrap();
            next <= i || next > hi
        })),
    ensures
        complex_selector_loop(l, i, hi, cs, ks, np) is None,
{
}

/// The compound selector ends the complex selector.
pub proof fn lemma_cs_end(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    ks: Seq<Combinator>,
    np: bool,
    cmp: Seq<Simple>,
    next: int,
)
    requires
        compound_selector(l, i, hi, np) == Some((cmp, next)),
        i < next <= hi,
        skip_whitespace(l, next, hi) >= hi,
    ensures
        complex_selector_loop(l, i, hi, cs, ks, np) == Some(
            Complex { compounds: cs.push(cmp), combinators: ks },
        ),
{
}

/// Something follows a pseudo-element: the complex selector fails.
pub proof fn lemma_cs_pseudo(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    ks: Seq<Combinator>,
    np: bool,
    cmp: Seq<Simple>,
    next: int,
)
    requires
        compound_selector(l, i, hi, np) == Some((cmp, next)),
        i < next <= hi,
        skip_whitespace(l, next, hi) < hi,
        has_pseudo_element(cmp),
    ensures
        complex_selector_loop(l, i, hi, cs, ks, np) is None,
{
}

/// A combinator follows, and another compound selector after it.
pub proof fn lemma_cs_combinator(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    ks: Seq<Combinator>,
    np: bool,
    cmp: Seq<Simple>,
    next: int,
    c: Combinator,
)
    requires
        compound_selector(l, i, hi, np) == Some((cmp, next)),
        i < next <= hi,
        skip_whitespace(l, next, hi) < hi,
        !has_pseudo_element(cmp),
        combinator_at(l, skip_whitespace(l, next, hi), hi) == Some(c),
    ensures
        skip_whitespace(l, skip_whitespace(l, next, hi) + 1, hi) >= hi ==> complex_selector_loop(
            l,
            i,
            hi,
            cs,
            ks,
            np,
        ) is None,
        skip_whitespace(l, skip_whitespace(l, next, hi) + 1, hi) < hi ==> complex_selector_loop(
            l,
            i,
            hi,
            cs,
            ks,
            np,
        ) == complex_selector_loop(
            l,
            skip_whitespace(l, skip_whitespace(l, next, hi) + 1, hi),
            hi,
            cs.push(cmp),
            ks.push(c),
            np,
        ),
{
}

/// No combinator follows: white space between the compound selectors is the descendant
/// combinator, and without it the complex selector fails.
pub proof fn lemma_cs_descendant(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    cs: Seq<Seq<Simple>>,
    ks: Seq<Combinator>,
    np: bool,
    cmp: Seq<Simple>,
    next: int,
)
    requires
        compound_selector(l, i, hi, np) == Some((cmp, next)),
        i < next <= hi,
        skip_whitespace(l, next, hi) < hi,
        !has_pseudo_element(cmp),
        combinator_at(l, skip_whitespace(l, next, hi), hi) is None,
    ensures
        skip_whitespace(l, next, hi) > next ==> complex_selector_loop(l, i, hi, cs, ks, np)
            == complex_selector_loop(
            l,
            skip_whitespace(l, next, hi),
            hi,
            cs.push(cmp),
            ks.push(Combinator::Descendant),
            np,
        ),
        skip_whitespace(l, next, hi) <= next ==> complex_selector_loop(l, i, hi, cs, ks, np) is None,
{
}

/// A list item: its complex selector, then the rest of the list.
pub proof fn lemma_cl_step(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Complex>,
    np: bool,
    sel: Option<Complex>,
)
    requires
        0 <= i <= hi,
        hi <= l.len(),
        complex_selector(l, i, next_comma(l, i, hi), np) == sel,
    ensures
        sel is None ==> complex_list_loop(l, i, hi, acc, np) is None,
        sel is Some && next_comma(l, i, hi) >= hi ==> complex_list_loop(l, i, hi, acc, np) == Some(
            acc.push(sel.unwrap()),
        ),
        sel is Some && next_comma(l, i, hi) < hi ==> complex_list_loop(l, i, hi, acc, np)
            == complex_list_loop(l, next_comma(l, i, hi) + 1, hi, acc.push(sel.unwrap()), np),
{
    lemma_next_comma_bounds(l, i, hi);
}

/// The list item starts past the end: the list fails.
pub proof fn lemma_cl_past(l: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>, np: bool)
    requires
        i > hi,
    ensures
        complex_list_loop(l, i, hi, acc, np) is None,
{
}

/// A forgiving list item: its complex selector, if it has one, then the rest of the list.
pub proof fn lemma_fl_step(
    l: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Complex>,
    sel: Option<Complex>,
)
    requires
        0 <= i < hi,
        hi <= l.len(),
        complex_selector(l, i, next_comma(l, i, hi), true) == sel,
    ensures
        ({
            let kept = match sel {
                Some(s) => acc.push(s),
                None => acc,
            };
            &&& next_comma(l, i, hi) >= hi ==> forgiving_list_loop(l, i, hi, acc) == kept
            &&& next_comma(l, i, hi) < hi ==> forgiving_list_loop(l, i, hi, acc) == forgiving_list_loop(
                l,
                next_comma(l, i, hi) + 1,
                hi,
                kept,
            )
        }),
{
    lemma_next_comma_bounds(l, i, hi);
}

/// Past the end, the forgiving list is what was kept.
pub proof fn lemma_fl_end(l: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>)
    requires
        i >= hi,
    ensures
        forgiving_list_loop(l, i, hi, acc) == acc,
{
}

} // verus!
