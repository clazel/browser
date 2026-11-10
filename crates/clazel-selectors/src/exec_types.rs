//! What the exec parser builds, and what each piece means in terms of [`super::spec`].
//!
//! The spec's selectors are trees: `:is()` holds a list of complex selectors. The exec ones
//! are flat arrays with ranges into each other, as `clazel-css`'s rows are, so that nothing
//! is nested in memory. A list of complex selectors is a range of `complexes`; a complex
//! selector is a range of `compounds` and one of `combinators`; a compound selector is a
//! range of `simples`; and `:is()`, `:where()` and `:not()` name a list by its index in
//! `lists`. The parser finishes a list before the list that holds it, so an argument's list
//! always has a smaller index, which is what makes the view below well-founded.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`AttrTest`], in memory.
#[derive(Debug, PartialEq, Eq)]
pub struct ExecAttrTest {
    /// The matcher.
    pub matcher: AttrMatcher,
    /// The value.
    pub value: Vec<u32>,
    /// The flag.
    pub flag: Option<CaseFlag>,
}

/// [`Simple`], in memory. An argument is the index of its list in [`ExecSelectors::lists`].
#[derive(Debug, PartialEq, Eq)]
pub enum ExecSimple {
    /// [`Simple::Type`].
    Type {
        /// The namespace component.
        ns: NsPrefix,
        /// The name.
        name: Vec<u32>,
    },
    /// [`Simple::Universal`].
    Universal {
        /// The namespace component.
        ns: NsPrefix,
    },
    /// [`Simple::Id`].
    Id {
        /// The identifier.
        name: Vec<u32>,
    },
    /// [`Simple::Class`].
    Class {
        /// The identifier.
        name: Vec<u32>,
    },
    /// [`Simple::Attribute`].
    Attribute {
        /// The namespace component.
        ns: NsPrefix,
        /// The name.
        name: Vec<u32>,
        /// The test.
        test: Option<ExecAttrTest>,
    },
    /// [`Simple::PseudoClass`].
    PseudoClass {
        /// Which.
        class: PseudoClass,
    },
    /// [`Simple::Nth`].
    Nth {
        /// Which.
        kind: NthKind,
        /// A.
        a: i32,
        /// B.
        b: i32,
    },
    /// [`Simple::Is`].
    Is {
        /// The argument's list.
        list: usize,
    },
    /// [`Simple::Where`].
    Where {
        /// The argument's list.
        list: usize,
    },
    /// [`Simple::Not`].
    Not {
        /// The argument's list.
        list: usize,
    },
    /// [`Simple::PseudoElement`].
    PseudoElement {
        /// Which.
        element: PseudoElement,
    },
}

/// A range `lo` up to `hi` of one of the arrays.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecRange {
    /// The first index.
    pub lo: usize,
    /// The index after the last.
    pub hi: usize,
}

/// A complex selector: its compound selectors and its combinators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecComplex {
    /// A range of [`ExecSelectors::compounds`].
    pub compounds: ExecRange,
    /// A range of [`ExecSelectors::combinators`].
    pub combinators: ExecRange,
}

/// Parsed selectors: the arrays, and the list that is the result, the last of `lists`.
#[derive(Debug, PartialEq, Eq)]
pub struct ExecSelectors {
    /// Simple selectors.
    pub simples: Vec<ExecSimple>,
    /// Compound selectors, as ranges of `simples`.
    pub compounds: Vec<ExecRange>,
    /// Combinators.
    pub combinators: Vec<Combinator>,
    /// Complex selectors.
    pub complexes: Vec<ExecComplex>,
    /// Lists of complex selectors, as ranges of `complexes`.
    pub lists: Vec<ExecRange>,
}

/// The view of an attribute test.
pub open spec fn view_test(test: Option<ExecAttrTest>) -> Option<AttrTest> {
    match test {
        Some(t) => Some(AttrTest { matcher: t.matcher, value: t.value@, flag: t.flag }),
        None => None,
    }
}

/// The simple selector at `si`, in a list whose index is `bound`: an argument's list must
/// come before it, or it is read as empty.
pub open spec fn view_simple(s: ExecSelectors, bound: int, si: int) -> Simple
    decreases bound, 0int, 0int,
{
    if si < 0 || si >= s.simples.len() {
        Simple::Universal { ns: NsPrefix::Absent }
    } else {
        match s.simples[si] {
            ExecSimple::Type { ns, name } => Simple::Type { ns, name: name@ },
            ExecSimple::Universal { ns } => Simple::Universal { ns },
            ExecSimple::Id { name } => Simple::Id { name: name@ },
            ExecSimple::Class { name } => Simple::Class { name: name@ },
            ExecSimple::Attribute { ns, name, test } => Simple::Attribute {
                ns,
                name: name@,
                test: view_test(test),
            },
            ExecSimple::PseudoClass { class } => Simple::PseudoClass { class },
            ExecSimple::Nth { kind, a, b } => Simple::Nth { kind, a: a as int, b: b as int },
            ExecSimple::Is { list } => Simple::Is {
                arg: if 0 <= list < bound {
                    view_list(s, list as int)
                } else {
                    Seq::empty()
                },
            },
            ExecSimple::Where { list } => Simple::Where {
                arg: if 0 <= list < bound {
                    view_list(s, list as int)
                } else {
                    Seq::empty()
                },
            },
            ExecSimple::Not { list } => Simple::Not {
                arg: if 0 <= list < bound {
                    view_list(s, list as int)
                } else {
                    Seq::empty()
                },
            },
            ExecSimple::PseudoElement { element } => Simple::PseudoElement { element },
        }
    }
}

/// The simple selectors `lo` up to `hi`.
pub open spec fn view_simples(s: ExecSelectors, bound: int, lo: int, hi: int) -> Seq<Simple>
    decreases bound, 1int, hi,
{
    if lo < 0 || hi <= lo || hi > s.simples.len() {
        Seq::empty()
    } else {
        view_simples(s, bound, lo, hi - 1).push(view_simple(s, bound, hi - 1))
    }
}

/// The compound selector at `ci`.
pub open spec fn view_compound(s: ExecSelectors, bound: int, ci: int) -> Seq<Simple>
    decreases bound, 2int, 0int,
{
    if ci < 0 || ci >= s.compounds.len() {
        Seq::empty()
    } else {
        view_simples(s, bound, s.compounds[ci].lo as int, s.compounds[ci].hi as int)
    }
}

/// The compound selectors `lo` up to `hi`.
pub open spec fn view_compounds(s: ExecSelectors, bound: int, lo: int, hi: int) -> Seq<Seq<Simple>>
    decreases bound, 3int, hi,
{
    if lo < 0 || hi <= lo || hi > s.compounds.len() {
        Seq::empty()
    } else {
        view_compounds(s, bound, lo, hi - 1).push(view_compound(s, bound, hi - 1))
    }
}

/// The combinators of a range.
pub open spec fn view_combinators(s: ExecSelectors, r: ExecRange) -> Seq<Combinator> {
    if r.lo <= r.hi <= s.combinators.len() {
        s.combinators@.subrange(r.lo as int, r.hi as int)
    } else {
        Seq::empty()
    }
}

/// The complex selector at `ci`.
pub open spec fn view_complex(s: ExecSelectors, bound: int, ci: int) -> Complex
    decreases bound, 4int, 0int,
{
    if ci < 0 || ci >= s.complexes.len() {
        Complex { compounds: Seq::empty(), combinators: Seq::empty() }
    } else {
        let c = s.complexes[ci];
        Complex {
            compounds: view_compounds(s, bound, c.compounds.lo as int, c.compounds.hi as int),
            combinators: view_combinators(s, c.combinators),
        }
    }
}

/// The complex selectors `lo` up to `hi`.
pub open spec fn view_complexes(s: ExecSelectors, bound: int, lo: int, hi: int) -> Seq<Complex>
    decreases bound, 5int, hi,
{
    if lo < 0 || hi <= lo || hi > s.complexes.len() {
        Seq::empty()
    } else {
        view_complexes(s, bound, lo, hi - 1).push(view_complex(s, bound, hi - 1))
    }
}

/// The list at `li`.
pub open spec fn view_list(s: ExecSelectors, li: int) -> Seq<Complex>
    decreases li, 6int, 0int,
{
    if li < 0 || li >= s.lists.len() {
        Seq::empty()
    } else {
        view_complexes(s, li, s.lists[li].lo as int, s.lists[li].hi as int)
    }
}

/// The result: the last list.
pub open spec fn view_selectors(s: ExecSelectors) -> Seq<Complex> {
    view_list(s, s.lists.len() - 1)
}

/// The arrays' ranges are in bounds and in order, and each argument's list comes before
/// the list that holds it. Every parse gives this.
pub open spec fn ranges_wf(s: ExecSelectors) -> bool {
    &&& forall|i: int|
        0 <= i < s.compounds.len() ==> #[trigger] s.compounds[i].lo <= s.compounds[i].hi
            <= s.simples.len()
    &&& forall|i: int|
        0 <= i < s.complexes.len() ==> {
            &&& #[trigger] s.complexes[i].compounds.lo <= s.complexes[i].compounds.hi
                <= s.compounds.len()
            &&& s.complexes[i].combinators.lo <= s.complexes[i].combinators.hi
                <= s.combinators.len()
        }
    &&& forall|i: int| 0 <= i < s.lists.len() ==> #[trigger] s.lists[i].lo <= s.lists[i].hi <= s.complexes.len()
    &&& s.simples.len() < usize::MAX
    &&& s.compounds.len() < usize::MAX
    &&& s.complexes.len() < usize::MAX
    &&& s.lists.len() < usize::MAX
}

/// The item at `i` of a slice that has one.
pub fn item<T>(v: &[T], i: usize) -> (r: &T)
    requires
        i < v@.len(),
    ensures
        *r == v@[i as int],
{
    match v.get(i) {
        Some(x) => x,
        None => vstd::pervasive::unreached(),
    }
}

// ------------------------------------------------------------------------------------
// Indexing the views
// ------------------------------------------------------------------------------------

/// [`view_simples`] is the simple selectors in order.
pub proof fn lemma_view_simples(s: ExecSelectors, bound: int, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.simples.len(),
    ensures
        view_simples(s, bound, lo, hi).len() == hi - lo,
        forall|k: int| 0 <= k < hi - lo ==> #[trigger] view_simples(s, bound, lo, hi)[k] == view_simple(s, bound, lo + k),
    decreases hi - lo,
{
    if hi > lo {
        lemma_view_simples(s, bound, lo, hi - 1);
    }
}

/// [`view_compounds`] is the compound selectors in order.
pub proof fn lemma_view_compounds(s: ExecSelectors, bound: int, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.compounds.len(),
    ensures
        view_compounds(s, bound, lo, hi).len() == hi - lo,
        forall|k: int| 0 <= k < hi - lo ==> #[trigger] view_compounds(s, bound, lo, hi)[k] == view_compound(s, bound, lo + k),
    decreases hi - lo,
{
    if hi > lo {
        lemma_view_compounds(s, bound, lo, hi - 1);
    }
}

/// [`view_complexes`] is the complex selectors in order.
pub proof fn lemma_view_complexes(s: ExecSelectors, bound: int, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.complexes.len(),
    ensures
        view_complexes(s, bound, lo, hi).len() == hi - lo,
        forall|k: int| 0 <= k < hi - lo ==> #[trigger] view_complexes(s, bound, lo, hi)[k] == view_complex(s, bound, lo + k),
    decreases hi - lo,
{
    if hi > lo {
        lemma_view_complexes(s, bound, lo, hi - 1);
    }
}

/// The views of a list's pieces, in a well-formed arena.
pub proof fn lemma_view_list(s: ExecSelectors, li: int)
    requires
        ranges_wf(s),
        0 <= li < s.lists.len(),
    ensures
        view_list(s, li).len() == s.lists[li].hi - s.lists[li].lo,
        forall|k: int|
            0 <= k < view_list(s, li).len() ==> #[trigger] view_list(s, li)[k] == view_complex(
                s,
                li,
                s.lists[li].lo + k,
            ),
{
    lemma_view_complexes(s, li, s.lists[li].lo as int, s.lists[li].hi as int);
}

/// The views of a complex selector's pieces, in a well-formed arena.
pub proof fn lemma_view_complex(s: ExecSelectors, bound: int, ci: int)
    requires
        ranges_wf(s),
        0 <= ci < s.complexes.len(),
    ensures
        ({
            let c = s.complexes[ci];
            let v = view_complex(s, bound, ci);
            &&& v.compounds.len() == c.compounds.hi - c.compounds.lo
            &&& forall|k: int|
                0 <= k < v.compounds.len() ==> #[trigger] v.compounds[k] == view_compound(
                    s,
                    bound,
                    c.compounds.lo + k,
                )
            &&& v.combinators.len() == c.combinators.hi - c.combinators.lo
            &&& forall|k: int|
                0 <= k < v.combinators.len() ==> #[trigger] v.combinators[k]
                    == s.combinators@[c.combinators.lo + k]
        }),
{
    let c = s.complexes[ci];
    lemma_view_compounds(s, bound, c.compounds.lo as int, c.compounds.hi as int);
}

/// The view of a compound selector's simple selectors, in a well-formed arena.
pub proof fn lemma_view_compound(s: ExecSelectors, bound: int, ci: int)
    requires
        ranges_wf(s),
        0 <= ci < s.compounds.len(),
    ensures
        view_compound(s, bound, ci).len() == s.compounds[ci].hi - s.compounds[ci].lo,
        forall|k: int|
            0 <= k < view_compound(s, bound, ci).len() ==> #[trigger] view_compound(s, bound, ci)[k]
                == view_simple(s, bound, s.compounds[ci].lo + k),
{
    lemma_view_simples(s, bound, s.compounds[ci].lo as int, s.compounds[ci].hi as int);
}

} // verus!
