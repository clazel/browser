//! A check, proven sound, that parsed selectors are what matching needs: in-bounds arrays
//! ([`ranges_wf`]) and a well-formed result ([`list_wf`]). The parser runs it on what it
//! built, so that [`super::exec_match::matches`]'s requirements hold of every parse without
//! the parser itself being proven (see [`super::exec_parse`]).

#[cfg(verus_only)]
use super::contract::*;
use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What [`check`] establishes.
pub open spec fn checked(s: ExecSelectors) -> bool {
    &&& ranges_wf(s)
    &&& s.lists.len() > 0
    &&& list_wf(view_selectors(s), view_selectors(s).len() as int)
}

/// [`ranges_wf`].
fn ranges_ok(s: &ExecSelectors) -> (r: bool)
    ensures
        r ==> ranges_wf(*s),
{
    if s.simples.len() == usize::MAX || s.compounds.len() == usize::MAX || s.complexes.len()
        == usize::MAX || s.lists.len() == usize::MAX {
        return false;
    }
    let mut i: usize = 0;
    while i < s.compounds.len()
        invariant
            i <= s.compounds.len(),
            forall|j: int|
                0 <= j < i ==> #[trigger] s.compounds@[j].lo <= s.compounds@[j].hi <= s.simples.len(),
        decreases s.compounds.len() - i,
    {
        let r = item(s.compounds.as_slice(), i);
        if !(r.lo <= r.hi && r.hi <= s.simples.len()) {
            return false;
        }
        i = i.saturating_add(1);
    }
    let mut i: usize = 0;
    while i < s.complexes.len()
        invariant
            i <= s.complexes.len(),
            forall|j: int|
                0 <= j < i ==> {
                    &&& #[trigger] s.complexes@[j].compounds.lo <= s.complexes@[j].compounds.hi
                        <= s.compounds.len()
                    &&& s.complexes@[j].combinators.lo <= s.complexes@[j].combinators.hi
                        <= s.combinators.len()
                },
        decreases s.complexes.len() - i,
    {
        let c = item(s.complexes.as_slice(), i);
        if !(c.compounds.lo <= c.compounds.hi && c.compounds.hi <= s.compounds.len()
            && c.combinators.lo <= c.combinators.hi && c.combinators.hi <= s.combinators.len()) {
            return false;
        }
        i = i.saturating_add(1);
    }
    let mut i: usize = 0;
    while i < s.lists.len()
        invariant
            i <= s.lists.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] s.lists@[j].lo <= s.lists@[j].hi <= s.complexes.len(),
        decreases s.lists.len() - i,
    {
        let r = item(s.lists.as_slice(), i);
        if !(r.lo <= r.hi && r.hi <= s.complexes.len()) {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// The simple selector at `si`, in the list `bound`, is well-formed.
fn simple_ok(s: &ExecSelectors, bound: usize, si: usize) -> (r: bool)
    requires
        ranges_wf(*s),
        si < s.simples.len(),
        bound <= s.lists.len(),
    ensures
        r ==> simple_wf(view_simple(*s, bound as int, si as int)),
    decreases bound, 0int,
{
    match item(s.simples.as_slice(), si) {
        ExecSimple::Is { list } => *list >= bound || list_ok(s, *list),
        ExecSimple::Where { list } => *list >= bound || list_ok(s, *list),
        ExecSimple::Not { list } => {
            if *list >= bound {
                return false;
            }
            let r = item(s.lists.as_slice(), *list);
            proof {
                lemma_view_list(*s, *list as int);
            }
            r.lo < r.hi && list_ok(s, *list)
        },
        _ => true,
    }
}

/// The compound selector at `ci`, in the list `bound`, is well-formed and not empty.
fn compound_ok(s: &ExecSelectors, bound: usize, ci: usize) -> (r: bool)
    requires
        ranges_wf(*s),
        ci < s.compounds.len(),
        bound <= s.lists.len(),
    ensures
        r ==> view_compound(*s, bound as int, ci as int).len() > 0 && compound_wf(
            view_compound(*s, bound as int, ci as int),
            view_compound(*s, bound as int, ci as int).len() as int,
        ),
    decreases bound, 1int,
{
    let ghost v = view_compound(*s, bound as int, ci as int);
    proof {
        lemma_view_compound(*s, bound as int, ci as int);
    }
    let lo = item(s.compounds.as_slice(), ci).lo;
    let hi = item(s.compounds.as_slice(), ci).hi;
    if lo >= hi {
        return false;
    }
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            lo <= k <= hi <= s.simples.len(),
            bound <= s.lists.len(),
            v == view_compound(*s, bound as int, ci as int),
            v.len() == hi - lo,
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_simple(*s, bound as int, lo + j),
            compound_wf(v, k - lo),
        decreases hi - k,
    {
        if !simple_ok(s, bound, k) {
            return false;
        }
        proof {
            assert(v[k - lo] == view_simple(*s, bound as int, k as int));
        }
        k = k.saturating_add(1);
    }
    true
}

/// The complex selector at `ci`, in the list `bound`, is well-formed.
fn complex_ok(s: &ExecSelectors, bound: usize, ci: usize) -> (r: bool)
    requires
        ranges_wf(*s),
        ci < s.complexes.len(),
        bound <= s.lists.len(),
    ensures
        r ==> complex_wf(view_complex(*s, bound as int, ci as int)),
    decreases bound, 2int,
{
    let ghost c = view_complex(*s, bound as int, ci as int);
    proof {
        lemma_view_complex(*s, bound as int, ci as int);
    }
    let cx = *item(s.complexes.as_slice(), ci);
    let n = cx.compounds.hi.saturating_sub(cx.compounds.lo);
    let m = cx.combinators.hi.saturating_sub(cx.combinators.lo);
    if n == 0 || m.saturating_add(1) != n {
        return false;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            ranges_wf(*s),
            bound <= s.lists.len(),
            ci < s.complexes.len(),
            cx == s.complexes@[ci as int],
            c == view_complex(*s, bound as int, ci as int),
            n == c.compounds.len(),
            cx.compounds.lo + n <= s.compounds.len(),
            forall|j: int| 0 <= j < n ==> #[trigger] c.compounds[j] == view_compound(*s, bound as int, cx.compounds.lo + j),
            k <= n,
            compounds_wf(c, k as int),
        decreases n - k,
    {
        if !compound_ok(s, bound, cx.compounds.lo.saturating_add(k)) {
            return false;
        }
        proof {
            assert(c.compounds[k as int] == view_compound(*s, bound as int, cx.compounds.lo + k));
        }
        k = k.saturating_add(1);
    }
    true
}

/// The list at `li` is well-formed.
fn list_ok(s: &ExecSelectors, li: usize) -> (r: bool)
    requires
        ranges_wf(*s),
        li < s.lists.len(),
    ensures
        r ==> list_wf(view_list(*s, li as int), view_list(*s, li as int).len() as int),
    decreases li, 3int,
{
    let ghost v = view_list(*s, li as int);
    proof {
        lemma_view_list(*s, li as int);
    }
    let lo = item(s.lists.as_slice(), li).lo;
    let hi = item(s.lists.as_slice(), li).hi;
    let mut k = lo;
    while k < hi
        invariant
            ranges_wf(*s),
            li < s.lists.len(),
            lo <= k <= hi <= s.complexes.len(),
            v == view_list(*s, li as int),
            v.len() == hi - lo,
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_complex(*s, li as int, lo + j),
            list_wf(v, k - lo),
        decreases hi - k,
    {
        if !complex_ok(s, li, k) {
            return false;
        }
        proof {
            assert(v[k - lo] == view_complex(*s, li as int, k as int));
        }
        k = k.saturating_add(1);
    }
    true
}

/// True only if `s` is [`checked`].
pub fn check(s: &ExecSelectors) -> (r: bool)
    ensures
        r ==> checked(*s),
{
    ranges_ok(s) && !s.lists.is_empty() && list_ok(s, s.lists.len().saturating_sub(1))
}

} // verus!
