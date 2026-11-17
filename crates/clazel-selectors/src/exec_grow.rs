//! What appending to the arrays of [`ExecSelectors`] leaves as it was: the parser only ever
//! appends, so the views of what it built earlier do not change, which is what lets each
//! step of [`super::exec_parse`] be proven on its own.
//!
//! A simple selector, compound selector or complex selector that is built but not yet in a
//! list is *pending*: it is viewed in the state where it is built, with `bound` the number
//! of lists there are, and every list it names is below that. The lemmas say that a pending
//! one means the same in every later state, and in the list that finally holds it.

use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `b` is `a` with more appended to each array.
pub open spec fn grows(a: ExecSelectors, b: ExecSelectors) -> bool {
    &&& a.simples.len() <= b.simples.len()
    &&& forall|i: int| 0 <= i < a.simples.len() ==> #[trigger] b.simples[i] == a.simples[i]
    &&& a.compounds.len() <= b.compounds.len()
    &&& forall|i: int| 0 <= i < a.compounds.len() ==> #[trigger] b.compounds[i] == a.compounds[i]
    &&& a.combinators.len() <= b.combinators.len()
    &&& forall|i: int| 0 <= i < a.combinators.len() ==> #[trigger] b.combinators[i] == a.combinators[i]
    &&& a.complexes.len() <= b.complexes.len()
    &&& forall|i: int| 0 <= i < a.complexes.len() ==> #[trigger] b.complexes[i] == a.complexes[i]
    &&& a.lists.len() <= b.lists.len()
    &&& forall|i: int| 0 <= i < a.lists.len() ==> #[trigger] b.lists[i] == a.lists[i]
}

/// Growing is transitive.
pub proof fn lemma_grows_trans(a: ExecSelectors, b: ExecSelectors, c: ExecSelectors)
    requires
        grows(a, b),
        grows(b, c),
    ensures
        grows(a, c),
{
    assert forall|i: int| 0 <= i < a.simples.len() implies c.simples[i] == a.simples[i] by {
        assert(b.simples[i] == a.simples[i]);
    }
    assert forall|i: int| 0 <= i < a.compounds.len() implies c.compounds[i] == a.compounds[i] by {
        assert(b.compounds[i] == a.compounds[i]);
    }
    assert forall|i: int| 0 <= i < a.combinators.len() implies c.combinators[i] == a.combinators[i] by {
        assert(b.combinators[i] == a.combinators[i]);
    }
    assert forall|i: int| 0 <= i < a.complexes.len() implies c.complexes[i] == a.complexes[i] by {
        assert(b.complexes[i] == a.complexes[i]);
    }
    assert forall|i: int| 0 <= i < a.lists.len() implies c.lists[i] == a.lists[i] by {
        assert(b.lists[i] == a.lists[i]);
    }
}

/// Growing is reflexive.
pub proof fn lemma_grows_refl(a: ExecSelectors)
    ensures
        grows(a, a),
{
}

/// The list `e` names, if any, is below `n`.
pub open spec fn ref_lt(e: ExecSimple, n: int) -> bool {
    match e {
        ExecSimple::Is { list } => list < n,
        ExecSimple::Where { list } => list < n,
        ExecSimple::Not { list } => list < n,
        _ => true,
    }
}

/// Every simple selector built names a list that was already built.
pub open spec fn refs_lt(s: ExecSelectors) -> bool {
    forall|si: int| 0 <= si < s.simples.len() ==> #[trigger] ref_lt(s.simples[si], s.lists.len() as int)
}

/// The simple selectors `acc`, pending in `s`, are in order what they mean there.
pub open spec fn pv_seq(s: ExecSelectors, acc: Seq<ExecSimple>) -> Seq<Simple> {
    acc.map_values(|e: ExecSimple| view_exec_simple(s, s.lists.len() as int, e))
}

/// Every pending simple selector names a list that is built.
pub open spec fn acc_in(s: ExecSelectors, acc: Seq<ExecSimple>) -> bool {
    forall|k: int| 0 <= k < acc.len() ==> #[trigger] ref_lt(acc[k], s.lists.len() as int)
}

/// The complex selector `c`, pending in `s`.
pub open spec fn pv_complex(s: ExecSelectors, c: ExecComplex) -> Complex {
    view_complex_of(s, s.lists.len() as int, c)
}

/// The ranges of `c` are those of arrays of `s`.
pub open spec fn complex_in(s: ExecSelectors, c: ExecComplex) -> bool {
    &&& c.compounds.lo <= c.compounds.hi <= s.compounds.len()
    &&& c.combinators.lo <= c.combinators.hi <= s.combinators.len()
}

/// Every pending complex selector is in `s`.
pub open spec fn cs_in(s: ExecSelectors, cs: Seq<ExecComplex>) -> bool {
    forall|k: int| 0 <= k < cs.len() ==> #[trigger] complex_in(s, cs[k])
}

/// The pending complex selectors, in order.
pub open spec fn pv_complexes(s: ExecSelectors, cs: Seq<ExecComplex>) -> Seq<Complex> {
    cs.map_values(|c: ExecComplex| pv_complex(s, c))
}

// ------------------------------------------------------------------------------------
// Views agree
// ------------------------------------------------------------------------------------

/// The lists below both bounds read the same in `a` and `b`.
pub open spec fn lists_agree(a: ExecSelectors, b: ExecSelectors, ba: int, bb: int) -> bool {
    forall|l: int| 0 <= l < ba && l < bb ==> #[trigger] view_list(a, l) == view_list(b, l)
}

/// Each simple selector of `a` names a list below both bounds or below neither.
pub open spec fn refs_agree(a: ExecSelectors, ba: int, bb: int) -> bool {
    forall|si: int|
        0 <= si < a.simples.len() ==> #[trigger] ref_lt(a.simples[si], ba) == ref_lt(
            a.simples[si],
            bb,
        )
}

/// The simple selectors of a range read the same.
pub proof fn lemma_agree_simples(
    a: ExecSelectors,
    b: ExecSelectors,
    ba: int,
    bb: int,
    lo: int,
    hi: int,
)
    requires
        grows(a, b),
        lists_agree(a, b, ba, bb),
        refs_agree(a, ba, bb),
        0 <= lo <= hi <= a.simples.len(),
    ensures
        view_simples(b, bb, lo, hi) == view_simples(a, ba, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_agree_simples(a, b, ba, bb, lo, hi - 1);
        let e = a.simples[hi - 1];
        assert(b.simples[hi - 1] == e);
        assert(ref_lt(e, ba) == ref_lt(e, bb));
        match e {
            ExecSimple::Is { list } => {
                if list < ba {
                    assert(view_list(a, list as int) == view_list(b, list as int));
                }
            },
            ExecSimple::Where { list } => {
                if list < ba {
                    assert(view_list(a, list as int) == view_list(b, list as int));
                }
            },
            ExecSimple::Not { list } => {
                if list < ba {
                    assert(view_list(a, list as int) == view_list(b, list as int));
                }
            },
            _ => {},
        }
        assert(view_simple(b, bb, hi - 1) == view_simple(a, ba, hi - 1));
    }
}

/// The compound selectors of a range read the same.
pub proof fn lemma_agree_compounds(
    a: ExecSelectors,
    b: ExecSelectors,
    ba: int,
    bb: int,
    lo: int,
    hi: int,
)
    requires
        ranges_wf(a),
        grows(a, b),
        lists_agree(a, b, ba, bb),
        refs_agree(a, ba, bb),
        0 <= lo <= hi <= a.compounds.len(),
    ensures
        view_compounds(b, bb, lo, hi) == view_compounds(a, ba, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_agree_compounds(a, b, ba, bb, lo, hi - 1);
        let r = a.compounds[hi - 1];
        assert(b.compounds[hi - 1] == r);
        assert(r.lo <= r.hi <= a.simples.len());
        lemma_agree_simples(a, b, ba, bb, r.lo as int, r.hi as int);
        assert(view_compound(b, bb, hi - 1) == view_compound(a, ba, hi - 1));
    }
}

/// A complex selector in `a` reads the same.
pub proof fn lemma_agree_complex_of(
    a: ExecSelectors,
    b: ExecSelectors,
    ba: int,
    bb: int,
    c: ExecComplex,
)
    requires
        ranges_wf(a),
        grows(a, b),
        lists_agree(a, b, ba, bb),
        refs_agree(a, ba, bb),
        complex_in(a, c),
    ensures
        view_complex_of(b, bb, c) == view_complex_of(a, ba, c),
{
    lemma_agree_compounds(a, b, ba, bb, c.compounds.lo as int, c.compounds.hi as int);
    assert(view_combinators(b, c.combinators) =~= view_combinators(a, c.combinators));
}

/// The complex selectors of a range read the same.
pub proof fn lemma_agree_complexes(
    a: ExecSelectors,
    b: ExecSelectors,
    ba: int,
    bb: int,
    lo: int,
    hi: int,
)
    requires
        ranges_wf(a),
        grows(a, b),
        lists_agree(a, b, ba, bb),
        refs_agree(a, ba, bb),
        0 <= lo <= hi <= a.complexes.len(),
    ensures
        view_complexes(b, bb, lo, hi) == view_complexes(a, ba, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_agree_complexes(a, b, ba, bb, lo, hi - 1);
        let c = a.complexes[hi - 1];
        assert(b.complexes[hi - 1] == c);
        lemma_agree_complex_of(a, b, ba, bb, c);
        assert(view_complex(b, bb, hi - 1) == view_complex(a, ba, hi - 1));
    }
}

/// The lists below `bound` read the same after growing.
pub proof fn lemma_grow_lists(a: ExecSelectors, b: ExecSelectors, bound: int)
    requires
        ranges_wf(a),
        grows(a, b),
        0 <= bound <= a.lists.len(),
    ensures
        forall|l: int| 0 <= l < bound ==> #[trigger] view_list(b, l) == view_list(a, l),
    decreases bound,
{
    if bound > 0 {
        lemma_grow_lists(a, b, bound - 1);
        let l = bound - 1;
        assert(lists_agree(b, a, l, l)) by {
            assert forall|k: int| 0 <= k < l && k < l implies view_list(b, k) == view_list(a, k) by {}
        }
        assert(lists_agree(a, b, l, l)) by {
            assert forall|k: int| 0 <= k < l && k < l implies view_list(a, k) == view_list(b, k) by {}
        }
        assert(refs_agree(a, l, l));
        let r = a.lists[l];
        assert(b.lists[l] == r);
        lemma_agree_complexes(a, b, l, l, r.lo as int, r.hi as int);
    }
}

/// A pending simple selector means the same in a later state, and in the list that holds
/// it.
pub proof fn lemma_stable_simple(a: ExecSelectors, b: ExecSelectors, bb: int, e: ExecSimple)
    requires
        ranges_wf(a),
        grows(a, b),
        ref_lt(e, a.lists.len() as int),
        a.lists.len() <= bb,
    ensures
        view_exec_simple(b, bb, e) == view_exec_simple(a, a.lists.len() as int, e),
{
    lemma_grow_lists(a, b, a.lists.len() as int);
    match e {
        ExecSimple::Is { list } => {
            assert(view_list(b, list as int) == view_list(a, list as int));
        },
        ExecSimple::Where { list } => {
            assert(view_list(b, list as int) == view_list(a, list as int));
        },
        ExecSimple::Not { list } => {
            assert(view_list(b, list as int) == view_list(a, list as int));
        },
        _ => {},
    }
}

/// A pending complex selector means the same in a later state, and in the list that holds
/// it.
pub proof fn lemma_stable_complex(a: ExecSelectors, b: ExecSelectors, bb: int, c: ExecComplex)
    requires
        ranges_wf(a),
        refs_lt(a),
        grows(a, b),
        complex_in(a, c),
        a.lists.len() <= bb,
    ensures
        view_complex_of(b, bb, c) == pv_complex(a, c),
{
    let ba = a.lists.len() as int;
    lemma_grow_lists(a, b, ba);
    assert(lists_agree(a, b, ba, bb)) by {
        assert forall|l: int| 0 <= l < ba && l < bb implies view_list(a, l) == view_list(b, l) by {
            assert(view_list(b, l) == view_list(a, l));
        }
    }
    assert(refs_agree(a, ba, bb)) by {
        assert forall|si: int| 0 <= si < a.simples.len() implies ref_lt(a.simples[si], ba) == ref_lt(
            a.simples[si],
            bb,
        ) by {
            assert(ref_lt(a.simples[si], ba));
        }
    }
    lemma_agree_complex_of(a, b, ba, bb, c);
}

} // verus!

