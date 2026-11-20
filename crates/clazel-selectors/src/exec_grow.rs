//! What appending to the arrays of [`ExecSelectors`] leaves as it was: the parser only ever
//! appends, so the views of what it built earlier do not change, which is what lets each
//! step of [`super::exec_parse`] be proven on its own.
//!
//! A simple selector, compound selector or complex selector that is built but not yet in a
//! list is *pending*: it is viewed in the state where it is built, with `bound` the number
//! of lists there are, and every list it names is below that. The lemmas say that a pending
//! one means the same in every later state, and in the list that finally holds it.

#[cfg(verus_only)]
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
#[verifier::opaque]
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
#[verifier::opaque]
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


/// Pending simple selectors mean the same in a later state.
pub proof fn lemma_pv_stable(a: ExecSelectors, b: ExecSelectors, acc: Seq<ExecSimple>)
    requires
        ranges_wf(a),
        grows(a, b),
        acc_in(a, acc),
    ensures
        pv_seq(b, acc) == pv_seq(a, acc),
        acc_in(b, acc),
{
    reveal(pv_seq);
    assert forall|k: int| 0 <= k < acc.len() implies pv_seq(b, acc)[k] == pv_seq(a, acc)[k] by {
        lemma_stable_simple(a, b, b.lists.len() as int, acc[k]);
    }
    assert(pv_seq(b, acc) =~= pv_seq(a, acc));
    assert forall|k: int| 0 <= k < acc.len() implies ref_lt(acc[k], b.lists.len() as int) by {
        assert(ref_lt(acc[k], a.lists.len() as int));
    }
}

/// One more pending complex selector.
pub proof fn lemma_pvc_push(s: ExecSelectors, cs: Seq<ExecComplex>, c: ExecComplex)
    ensures
        pv_complexes(s, cs.push(c)) == pv_complexes(s, cs).push(pv_complex(s, c)),
        pv_complexes(s, Seq::empty()) == Seq::<Complex>::empty(),
{
    reveal(pv_complexes);
    assert(pv_complexes(s, cs.push(c)) =~= pv_complexes(s, cs).push(pv_complex(s, c)));
    assert(pv_complexes(s, Seq::empty()) =~= Seq::<Complex>::empty());
}

/// Pending complex selectors mean the same in a later state.
pub proof fn lemma_pvc_stable(a: ExecSelectors, b: ExecSelectors, cs: Seq<ExecComplex>)
    requires
        ranges_wf(a),
        refs_lt(a),
        grows(a, b),
        cs_in(a, cs),
    ensures
        pv_complexes(b, cs) == pv_complexes(a, cs),
        cs_in(b, cs),
{
    reveal(pv_complexes);
    assert forall|k: int| 0 <= k < cs.len() implies pv_complexes(b, cs)[k] == pv_complexes(a, cs)[k] by {
        lemma_stable_complex(a, b, b.lists.len() as int, cs[k]);
    }
    assert(pv_complexes(b, cs) =~= pv_complexes(a, cs));
    assert forall|k: int| 0 <= k < cs.len() implies complex_in(b, cs[k]) by {
        assert(complex_in(a, cs[k]));
    }
}

/// One more pending simple selector, and none.
pub proof fn lemma_pv_push(s: ExecSelectors, acc: Seq<ExecSimple>, e: ExecSimple)
    ensures
        pv_seq(s, acc.push(e)) == pv_seq(s, acc).push(view_exec_simple(s, s.lists.len() as int, e)),
        pv_seq(s, Seq::empty()) == Seq::<Simple>::empty(),
        pv_seq(s, seq![e]) == seq![view_exec_simple(s, s.lists.len() as int, e)],
{
    reveal(pv_seq);
    assert(pv_seq(s, acc.push(e)) =~= pv_seq(s, acc).push(view_exec_simple(s, s.lists.len() as int, e)));
    assert(pv_seq(s, Seq::empty()) =~= Seq::<Simple>::empty());
    assert(pv_seq(s, seq![e]) =~= seq![view_exec_simple(s, s.lists.len() as int, e)]);
}

/// There is a view for each pending simple selector.
pub proof fn lemma_pv_len(s: ExecSelectors, acc: Seq<ExecSimple>)
    ensures
        pv_seq(s, acc).len() == acc.len(),
{
    reveal(pv_seq);
}

/// The view of one pending simple selector among others.
pub proof fn lemma_pv_index(s: ExecSelectors, acc: Seq<ExecSimple>, k: int)
    requires
        0 <= k < acc.len(),
    ensures
        pv_seq(s, acc).len() == acc.len(),
        pv_seq(s, acc)[k] == view_exec_simple(s, s.lists.len() as int, acc[k]),
{
    reveal(pv_seq);
}

/// One more pending compound selector, and none.
pub proof fn lemma_pvs_push(s: ExecSelectors, rs: Seq<ExecRange>, r: ExecRange)
    ensures
        pv_compounds(s, rs.push(r)) == pv_compounds(s, rs).push(
            view_simples(s, s.lists.len() as int, r.lo as int, r.hi as int),
        ),
        pv_compounds(s, Seq::empty()) == Seq::<Seq<Simple>>::empty(),
{
    reveal(pv_compounds);
    assert(pv_compounds(s, rs.push(r)) =~= pv_compounds(s, rs).push(
        view_simples(s, s.lists.len() as int, r.lo as int, r.hi as int),
    ));
    assert(pv_compounds(s, Seq::empty()) =~= Seq::<Seq<Simple>>::empty());
}

// ------------------------------------------------------------------------------------
// Pending compound selectors
// ------------------------------------------------------------------------------------

/// The ranges of `rs` are ranges of the simple selectors of `s`.
pub open spec fn ranges_in(s: ExecSelectors, rs: Seq<ExecRange>) -> bool {
    forall|k: int| 0 <= k < rs.len() ==> #[trigger] rs[k].lo <= rs[k].hi <= s.simples.len()
}

/// The compound selectors that the ranges `rs` of `s`'s simple selectors are, pending.
#[verifier::opaque]
pub open spec fn pv_compounds(s: ExecSelectors, rs: Seq<ExecRange>) -> Seq<Seq<Simple>> {
    rs.map_values(|r: ExecRange| view_simples(s, s.lists.len() as int, r.lo as int, r.hi as int))
}

/// The simple selectors of a range mean the same in a later state, and in the list that holds
/// them.
pub proof fn lemma_stable_simples(a: ExecSelectors, b: ExecSelectors, bb: int, lo: int, hi: int)
    requires
        ranges_wf(a),
        refs_lt(a),
        grows(a, b),
        a.lists.len() <= bb,
        0 <= lo <= hi <= a.simples.len(),
    ensures
        view_simples(b, bb, lo, hi) == view_simples(a, a.lists.len() as int, lo, hi),
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
    lemma_agree_simples(a, b, ba, bb, lo, hi);
}

/// Pending compound selectors mean the same in a later state.
pub proof fn lemma_stable_pv_compounds(a: ExecSelectors, b: ExecSelectors, rs: Seq<ExecRange>)
    requires
        ranges_wf(a),
        refs_lt(a),
        grows(a, b),
        ranges_in(a, rs),
    ensures
        pv_compounds(b, rs) == pv_compounds(a, rs),
{
    reveal(pv_compounds);
    assert forall|k: int| 0 <= k < rs.len() implies pv_compounds(b, rs)[k] == pv_compounds(a, rs)[k] by {
        lemma_stable_simples(a, b, b.lists.len() as int, rs[k].lo as int, rs[k].hi as int);
    }
    assert(pv_compounds(b, rs) =~= pv_compounds(a, rs));
}


// ------------------------------------------------------------------------------------
// Appending
// ------------------------------------------------------------------------------------

/// Appending the simple selectors `cv` of a compound selector.
#[verifier::spinoff_prover]
pub proof fn lemma_append_compound(s1: ExecSelectors, s2: ExecSelectors, cv: Seq<ExecSimple>)
    requires
        ranges_wf(s1),
        refs_lt(s1),
        acc_in(s1, cv),
        s2.simples@ =~= s1.simples@ + cv,
        s2.compounds@ =~= s1.compounds@,
        s2.combinators@ =~= s1.combinators@,
        s2.complexes@ =~= s1.complexes@,
        s2.lists@ =~= s1.lists@,
        s2.simples.len() < usize::MAX,
    ensures
        ranges_wf(s2),
        refs_lt(s2),
        grows(s1, s2),
        s2.lists.len() == s1.lists.len(),
        view_simples(
            s2,
            s2.lists.len() as int,
            s1.simples.len() as int,
            s2.simples.len() as int,
        ) == pv_seq(s1, cv),
{
    let first = s1.simples.len() as int;
    let end = s2.simples.len() as int;
    assert(s2.compounds.len() == s1.compounds.len());
    assert(s2.combinators.len() == s1.combinators.len());
    assert(s2.complexes.len() == s1.complexes.len());
    assert(s2.lists.len() == s1.lists.len());
    assert(grows(s1, s2)) by {
        assert forall|k: int| 0 <= k < s1.simples.len() implies s2.simples[k] == s1.simples[k] by {}
    }
    assert(ranges_wf(s2)) by {
        assert forall|k: int| 0 <= k < s2.compounds.len() implies #[trigger] s2.compounds[k].lo
            <= s2.compounds[k].hi <= s2.simples.len() by {
            assert(s2.compounds[k] == s1.compounds[k]);
        }
        assert forall|k: int| 0 <= k < s2.complexes.len() implies {
            &&& #[trigger] s2.complexes[k].compounds.lo <= s2.complexes[k].compounds.hi
                <= s2.compounds.len()
            &&& s2.complexes[k].combinators.lo <= s2.complexes[k].combinators.hi
                <= s2.combinators.len()
        } by {
            assert(s2.complexes[k] == s1.complexes[k]);
        }
        assert forall|k: int| 0 <= k < s2.lists.len() implies #[trigger] s2.lists[k].lo <= s2.lists[k].hi
            <= s2.complexes.len() by {
            assert(s2.lists[k] == s1.lists[k]);
        }
    }
    assert(refs_lt(s2)) by {
        assert forall|si: int| 0 <= si < s2.simples.len() implies #[trigger] ref_lt(
            s2.simples[si],
            s2.lists.len() as int,
        ) by {
            if si < s1.simples.len() {
                assert(s2.simples[si] == s1.simples[si]);
            } else {
                assert(s2.simples[si] == cv[si - first]);
            }
        }
    }
    reveal(pv_seq);
    lemma_view_simples(s2, s2.lists.len() as int, first, end);
    assert forall|k: int| 0 <= k < cv.len() implies view_simples(s2, s2.lists.len() as int, first, end)[k]
        == pv_seq(s1, cv)[k] by {
        lemma_view_simple_is(s2, s2.lists.len() as int, first + k);
        assert(s2.simples[first + k] == cv[k]);
        lemma_stable_simple(s1, s2, s2.lists.len() as int, cv[k]);
    }
    assert(view_simples(s2, s2.lists.len() as int, first, end) =~= pv_seq(s1, cv));
}

/// The pending compound selectors with one more, whose simple selectors were just appended.
pub proof fn lemma_compounds_push(
    s0: ExecSelectors,
    s1: ExecSelectors,
    s2: ExecSelectors,
    rs: Seq<ExecRange>,
    r: ExecRange,
    cv: Seq<ExecSimple>,
)
    requires
        ranges_wf(s0),
        refs_lt(s0),
        grows(s0, s1),
        grows(s1, s2),
        ranges_in(s0, rs),
        s2.lists.len() == s1.lists.len(),
        0 <= r.lo <= r.hi <= s2.simples.len(),
        view_simples(s2, s2.lists.len() as int, r.lo as int, r.hi as int) == pv_seq(s1, cv),
    ensures
        pv_compounds(s2, rs.push(r)) == pv_compounds(s0, rs).push(pv_seq(s1, cv)),
        ranges_in(s2, rs.push(r)),
{
    lemma_grows_trans(s0, s1, s2);
    lemma_stable_pv_compounds(s0, s2, rs);
    reveal(pv_compounds);
    assert(pv_compounds(s2, rs.push(r)) =~= pv_compounds(s2, rs).push(
        view_simples(s2, s2.lists.len() as int, r.lo as int, r.hi as int),
    ));
    assert forall|k: int| 0 <= k < rs.push(r).len() implies #[trigger] rs.push(r)[k].lo
        <= rs.push(r)[k].hi <= s2.simples.len() by {
        if k < rs.len() {
            assert(rs.push(r)[k] == rs[k]);
        }
    }
}

/// Appending the compound selectors `rs` and the combinators `ks` of a complex selector.
#[verifier::spinoff_prover]
pub proof fn lemma_append_complex(
    s2: ExecSelectors,
    s3: ExecSelectors,
    rs: Seq<ExecRange>,
    ks: Seq<Combinator>,
)
    requires
        ranges_wf(s2),
        refs_lt(s2),
        ranges_in(s2, rs),
        s3.simples@ =~= s2.simples@,
        s3.compounds@ =~= s2.compounds@ + rs,
        s3.combinators@ =~= s2.combinators@ + ks,
        s3.complexes@ =~= s2.complexes@,
        s3.lists@ =~= s2.lists@,
        s3.compounds.len() < usize::MAX,
        s3.combinators.len() < usize::MAX,
    ensures
        ranges_wf(s3),
        refs_lt(s3),
        grows(s2, s3),
        ({
            let r = ExecComplex {
                compounds: ExecRange {
                    lo: s2.compounds.len(),
                    hi: s3.compounds.len(),
                },
                combinators: ExecRange {
                    lo: s2.combinators.len(),
                    hi: s3.combinators.len(),
                },
            };
            &&& complex_in(s3, r)
            &&& pv_complex(s3, r) == (Complex { compounds: pv_compounds(s2, rs), combinators: ks })
        }),
{
    let c_lo = s2.compounds.len() as int;
    let c_hi = s3.compounds.len() as int;
    assert(s3.simples.len() == s2.simples.len());
    assert(s3.complexes.len() == s2.complexes.len());
    assert(s3.lists.len() == s2.lists.len());
    assert(s3.compounds.len() == s2.compounds.len() + rs.len());
    assert(s3.combinators.len() == s2.combinators.len() + ks.len());
    assert(s3.simples.len() < usize::MAX);
    assert(s3.complexes.len() < usize::MAX);
    assert(s3.lists.len() < usize::MAX);
    assert(s3.compounds.len() < usize::MAX);
    assert(grows(s2, s3)) by {
        assert forall|k: int| 0 <= k < s2.compounds.len() implies s3.compounds[k] == s2.compounds[k] by {}
        assert forall|k: int| 0 <= k < s2.combinators.len() implies s3.combinators[k] == s2.combinators[k] by {}
    }
    assert forall|k: int| 0 <= k < s3.compounds.len() implies #[trigger] s3.compounds[k].lo
        <= s3.compounds[k].hi <= s3.simples.len() by {
        if k < s2.compounds.len() {
            assert(s3.compounds[k] == s2.compounds[k]);
        } else {
            assert(s3.compounds[k] == rs[k - c_lo]);
            assert(rs[k - c_lo].lo <= rs[k - c_lo].hi <= s2.simples.len());
        }
    }
    assert forall|k: int| 0 <= k < s3.complexes.len() implies {
        &&& #[trigger] s3.complexes[k].compounds.lo <= s3.complexes[k].compounds.hi
            <= s3.compounds.len()
        &&& s3.complexes[k].combinators.lo <= s3.complexes[k].combinators.hi
            <= s3.combinators.len()
    } by {
        assert(s3.complexes[k] == s2.complexes[k]);
    }
    assert forall|k: int| 0 <= k < s3.lists.len() implies #[trigger] s3.lists[k].lo <= s3.lists[k].hi
        <= s3.complexes.len() by {
        assert(s3.lists[k] == s2.lists[k]);
    }
    assert(forall|i: int|
        0 <= i < s3.compounds.len() ==> #[trigger] s3.compounds[i].lo <= s3.compounds[i].hi
            <= s3.simples.len());
    assert(forall|i: int|
        0 <= i < s3.complexes.len() ==> {
            &&& #[trigger] s3.complexes[i].compounds.lo <= s3.complexes[i].compounds.hi
                <= s3.compounds.len()
            &&& s3.complexes[i].combinators.lo <= s3.complexes[i].combinators.hi
                <= s3.combinators.len()
        });
    assert(forall|i: int|
        0 <= i < s3.lists.len() ==> #[trigger] s3.lists[i].lo <= s3.lists[i].hi <= s3.complexes.len());
    assert(ranges_wf(s3));
    assert(refs_lt(s3)) by {
        assert forall|si: int| 0 <= si < s3.simples.len() implies #[trigger] ref_lt(
            s3.simples[si],
            s3.lists.len() as int,
        ) by {
            assert(s3.simples[si] == s2.simples[si]);
        }
    }
    let r = ExecComplex {
        compounds: ExecRange { lo: s2.compounds.len(), hi: s3.compounds.len() },
        combinators: ExecRange { lo: s2.combinators.len(), hi: s3.combinators.len() },
    };
    reveal(pv_compounds);
    lemma_view_compounds(s3, s3.lists.len() as int, c_lo, c_hi);
    assert forall|k: int| 0 <= k < rs.len() implies view_compounds(s3, s3.lists.len() as int, c_lo, c_hi)[k]
        == pv_compounds(s2, rs)[k] by {
        assert(s3.compounds[c_lo + k] == rs[k]);
        lemma_stable_simples(s2, s3, s3.lists.len() as int, rs[k].lo as int, rs[k].hi as int);
    }
    assert(view_compounds(s3, s3.lists.len() as int, c_lo, c_hi) =~= pv_compounds(s2, rs));
    assert(view_combinators(s3, r.combinators) =~= ks);
}

} // verus!
