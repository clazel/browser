//! §17 specificity, proven to meet [`super::contract::specificity_ensures`].

use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`Specificity`], in memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecSpecificity {
    /// A.
    pub a: u32,
    /// B.
    pub b: u32,
    /// C.
    pub c: u32,
}

/// The specificity an [`ExecSpecificity`] holds.
pub open spec fn view_specificity(x: ExecSpecificity) -> Specificity {
    Specificity { a: x.a as nat, b: x.b as nat, c: x.c as nat }
}

/// (0, 0, 0).
fn exec_zero() -> (r: ExecSpecificity)
    ensures
        view_specificity(r) == zero(),
{
    ExecSpecificity { a: 0, b: 0, c: 0 }
}

/// One component of [`add`].
fn saturating(x: u32, y: u32) -> (r: u32)
    ensures
        r as nat == saturate(x as nat + y as nat),
{
    x.saturating_add(y)
}

/// [`add`].
fn exec_add(x: ExecSpecificity, y: ExecSpecificity) -> (r: ExecSpecificity)
    ensures
        view_specificity(r) == add_specificity(view_specificity(x), view_specificity(y)),
{
    ExecSpecificity { a: saturating(x.a, y.a), b: saturating(x.b, y.b), c: saturating(x.c, y.c) }
}

/// [`most_specific`].
fn exec_most_specific(x: ExecSpecificity, y: ExecSpecificity) -> (r: ExecSpecificity)
    ensures
        view_specificity(r) == most_specific(view_specificity(x), view_specificity(y)),
{
    if x.a < y.a || (x.a == y.a && (x.b < y.b || (x.b == y.b && x.c <= y.c))) {
        y
    } else {
        x
    }
}

/// One (A, B, C) for a selector that counts once.
fn exec_one(a: u32, b: u32, c: u32) -> (r: ExecSpecificity)
    ensures
        r == (ExecSpecificity { a, b, c }),
{
    ExecSpecificity { a, b, c }
}

/// The specificity of the simple selector at `si`, in the list `bound`.
pub fn simple_specificity_of(s: &ExecSelectors, bound: usize, si: usize) -> (r: ExecSpecificity)
    requires
        ranges_wf(*s),
        si < s.simples.len(),
        bound <= s.lists.len(),
    ensures
        view_specificity(r) == simple_specificity(view_simple(*s, bound as int, si as int)),
    decreases bound, 0int, 0int,
{
    match item(s.simples.as_slice(), si) {
        ExecSimple::Id { .. } => exec_one(1, 0, 0),
        ExecSimple::Class { .. } => exec_one(0, 1, 0),
        ExecSimple::Attribute { .. } => exec_one(0, 1, 0),
        ExecSimple::PseudoClass { .. } => exec_one(0, 1, 0),
        ExecSimple::Nth { .. } => exec_one(0, 1, 0),
        ExecSimple::Type { .. } => exec_one(0, 0, 1),
        ExecSimple::PseudoElement { .. } => exec_one(0, 0, 1),
        ExecSimple::Universal { .. } => exec_zero(),
        ExecSimple::Is { list } => if *list < bound {
            list_specificity_of(s, *list)
        } else {
            exec_zero()
        },
        ExecSimple::Not { list } => if *list < bound {
            list_specificity_of(s, *list)
        } else {
            exec_zero()
        },
        ExecSimple::Where { .. } => exec_zero(),
    }
}

/// The specificity of the compound selector at `ci`, in the list `bound`.
fn compound_specificity_of(s: &ExecSelectors, bound: usize, ci: usize) -> (r: ExecSpecificity)
    requires
        ranges_wf(*s),
        ci < s.compounds.len(),
        bound <= s.lists.len(),
    ensures
        view_specificity(r) == compound_specificity(
            view_compound(*s, bound as int, ci as int),
            view_compound(*s, bound as int, ci as int).len() as int,
        ),
    decreases bound, 1int, 0int,
{
    let ghost v = view_compound(*s, bound as int, ci as int);
    proof {
        lemma_view_compound(*s, bound as int, ci as int);
    }
    let lo = item(s.compounds.as_slice(), ci).lo;
    let hi = item(s.compounds.as_slice(), ci).hi;
    let mut acc = exec_zero();
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            lo <= k <= hi <= s.simples.len(),
            bound <= s.lists.len(),
            v == view_compound(*s, bound as int, ci as int),
            v.len() == hi - lo,
            lo == s.compounds@[ci as int].lo,
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_simple(*s, bound as int, lo + j),
            view_specificity(acc) == compound_specificity(v, k - lo),
        decreases hi - k,
    {
        let one = simple_specificity_of(s, bound, k);
        acc = exec_add(acc, one);
        k = k.saturating_add(1);
        proof {
            assert(v[k - 1 - lo] == view_simple(*s, bound as int, (k - 1) as int));
        }
    }
    acc
}

/// The specificity of the complex selector at `ci`, in the list `bound`.
pub fn complex_specificity_of(s: &ExecSelectors, bound: usize, ci: usize) -> (r: ExecSpecificity)
    requires
        ranges_wf(*s),
        ci < s.complexes.len(),
        bound <= s.lists.len(),
    ensures
        view_specificity(r) == specificity(view_complex(*s, bound as int, ci as int)),
    decreases bound, 2int, 0int,
{
    let ghost v = view_complex(*s, bound as int, ci as int);
    proof {
        lemma_view_complex(*s, bound as int, ci as int);
    }
    let lo = item(s.complexes.as_slice(), ci).compounds.lo;
    let hi = item(s.complexes.as_slice(), ci).compounds.hi;
    let mut acc = exec_zero();
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            lo <= k <= hi <= s.compounds.len(),
            bound <= s.lists.len(),
            v == view_complex(*s, bound as int, ci as int),
            v.compounds.len() == hi - lo,
            forall|j: int|
                0 <= j < v.compounds.len() ==> #[trigger] v.compounds[j] == view_compound(
                    *s,
                    bound as int,
                    lo + j,
                ),
            view_specificity(acc) == complex_specificity(v, k - lo),
        decreases hi - k,
    {
        let one = compound_specificity_of(s, bound, k);
        acc = exec_add(acc, one);
        k = k.saturating_add(1);
        proof {
            assert(v.compounds[k - 1 - lo] == view_compound(*s, bound as int, (k - 1) as int));
        }
    }
    acc
}

/// The most specific complex selector of the list at `li`: the specificity of `:is()` or
/// `:not()` with that argument.
pub fn list_specificity_of(s: &ExecSelectors, li: usize) -> (r: ExecSpecificity)
    requires
        ranges_wf(*s),
        li < s.lists.len(),
    ensures
        view_specificity(r) == list_specificity(
            view_list(*s, li as int),
            view_list(*s, li as int).len() as int,
        ),
    decreases li, 3int, 0int,
{
    let ghost v = view_list(*s, li as int);
    proof {
        lemma_view_list(*s, li as int);
    }
    let lo = item(s.lists.as_slice(), li).lo;
    let hi = item(s.lists.as_slice(), li).hi;
    let mut acc = exec_zero();
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            lo <= k <= hi <= s.complexes.len(),
            li < s.lists.len(),
            v == view_list(*s, li as int),
            v.len() == hi - lo,
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_complex(*s, li as int, lo + j),
            view_specificity(acc) == list_specificity(v, k - lo),
        decreases hi - k,
    {
        let one = complex_specificity_of(s, li, k);
        acc = exec_most_specific(acc, one);
        k = k.saturating_add(1);
        proof {
            assert(v[k - 1 - lo] == view_complex(*s, li as int, (k - 1) as int));
        }
    }
    acc
}

} // verus!
