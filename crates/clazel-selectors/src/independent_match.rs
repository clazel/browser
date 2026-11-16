//! The independent transcription's matching ([`super::independent::i_match_selector`]) is equal to
//! the spec's ([`super::spec::match_a_selector_against_an_element`]) on the selectors the two have
//! in common ([`super::independent_equivalence::rel_list`]), in a well-formed arena whose
//! elements have no two attributes with the same namespace and local name.
//!
//! The two walk the tree differently, so most of this file is about the tree: the spec looks
//! at the children of a parent, the transcription at the element children among them
//! ([`i_elements`]); the spec follows parents for a bounded number of steps, the transcription
//! asks DOM's "descendant".

#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::independent_attr::*;
#[cfg(verus_only)]
use super::independent_equivalence::*;
#[cfg(verus_only)]
use super::lemmas::lemma_nth_index_matches;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use clazel_dom::lemmas::{
    lemma_index_of, lemma_index_of_unique, lemma_path, lemma_path_facts, lemma_wf_witness,
};
#[cfg(verus_only)]
use clazel_dom::spec::{inclusive_ancestor_within, index_of, is_descendant, parent, wf, wf_with};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Element children
// ------------------------------------------------------------------------------------

/// The number of elements among the first `j` of `ch`.
pub open spec fn cnt_el(doc: Document, ch: Seq<NodeId>, j: int) -> int {
    i_elements(doc, ch.subrange(0, j)).len() as int
}

/// The elements of a concatenation.
pub proof fn lemma_elements_append(doc: Document, s: Seq<NodeId>, t: Seq<NodeId>)
    ensures
        i_elements(doc, s + t) == i_elements(doc, s) + i_elements(doc, t),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s + t =~= t);
    } else {
        lemma_elements_append(doc, s.drop_first(), t);
        assert((s + t).drop_first() =~= s.drop_first() + t);
        assert((s + t)[0] == s[0]);
        if i_is_el(doc, s[0]) {
            assert(seq![s[0]] + i_elements(doc, s.drop_first()) + i_elements(doc, t)
                =~= seq![s[0]] + (i_elements(doc, s.drop_first()) + i_elements(doc, t)));
        }
    }
}

/// One more child.
pub proof fn lemma_cnt_step(doc: Document, ch: Seq<NodeId>, j: int)
    requires
        0 <= j < ch.len(),
    ensures
        cnt_el(doc, ch, j + 1) == cnt_el(doc, ch, j) + if i_is_el(doc, ch[j]) {
            1int
        } else {
            0int
        },
        i_elements(doc, ch.subrange(0, j + 1)) == i_elements(doc, ch.subrange(0, j)) + if i_is_el(
            doc,
            ch[j],
        ) {
            seq![ch[j]]
        } else {
            Seq::<NodeId>::empty()
        },
{
    assert(ch.subrange(0, j + 1) =~= ch.subrange(0, j) + seq![ch[j]]);
    lemma_elements_append(doc, ch.subrange(0, j), seq![ch[j]]);
    let one = seq![ch[j]];
    assert(one.drop_first().len() == 0);
    assert(i_elements(doc, one.drop_first()) =~= Seq::<NodeId>::empty());
    assert(i_elements(doc, seq![ch[j]]) =~= if i_is_el(doc, ch[j]) {
        seq![ch[j]]
    } else {
        Seq::<NodeId>::empty()
    });
}

/// The count of elements never decreases.
pub proof fn lemma_cnt_mono(doc: Document, ch: Seq<NodeId>, a: int, b: int)
    requires
        0 <= a <= b <= ch.len(),
    ensures
        cnt_el(doc, ch, a) <= cnt_el(doc, ch, b),
    decreases b - a,
{
    if a < b {
        lemma_cnt_step(doc, ch, a);
        lemma_cnt_mono(doc, ch, a + 1, b);
    }
}

/// The whole list's elements.
pub proof fn lemma_cnt_all(doc: Document, ch: Seq<NodeId>)
    ensures
        cnt_el(doc, ch, ch.len() as int) == i_elements(doc, ch).len(),
{
    assert(ch.subrange(0, ch.len() as int) =~= ch);
}

/// An element child sits in the element list at the count of the elements before it.
pub proof fn lemma_elements_nth(doc: Document, ch: Seq<NodeId>, j: int)
    requires
        0 <= j < ch.len(),
        i_is_el(doc, ch[j]),
    ensures
        0 <= cnt_el(doc, ch, j) < i_elements(doc, ch).len(),
        i_elements(doc, ch)[cnt_el(doc, ch, j)] == ch[j],
{
    let pre = ch.subrange(0, j);
    let post = ch.subrange(j, ch.len() as int);
    assert(ch =~= pre + post);
    lemma_elements_append(doc, pre, post);
    assert(post[0] == ch[j]);
    assert(post.drop_first().len() == post.len() - 1);
    assert(i_elements(doc, post) == seq![ch[j]] + i_elements(doc, post.drop_first()));
    assert(i_elements(doc, ch) == i_elements(doc, pre) + (seq![ch[j]] + i_elements(doc, post.drop_first())));
}

/// A list without duplicates has element children without duplicates.
pub proof fn lemma_elements_nodup(doc: Document, ch: Seq<NodeId>)
    requires
        ch.no_duplicates(),
    ensures
        i_elements(doc, ch).no_duplicates(),
    decreases ch.len(),
{
    if ch.len() > 0 {
        let r = ch.drop_first();
        assert forall|a: int, b: int| 0 <= a < r.len() && 0 <= b < r.len() && a != b implies r[a] != r[b] by {
            assert(r[a] == ch[a + 1] && r[b] == ch[b + 1]);
        }
        lemma_elements_nodup(doc, r);
        if i_is_el(doc, ch[0]) {
            let e = i_elements(doc, r);
            assert forall|k: int| 0 <= k < e.len() implies e[k] != ch[0] by {
                lemma_elements_in(doc, r, e[k]);
                let kk = choose|kk: int| 0 <= kk < r.len() && r[kk] == e[k];
                assert(ch[kk + 1] == e[k]);
            }
            let all = seq![ch[0]] + e;
            assert forall|a: int, b: int| 0 <= a < all.len() && 0 <= b < all.len() && a != b implies all[a] != all[b] by {
                if a == 0 {
                    assert(all[b] == e[b - 1]);
                } else if b == 0 {
                    assert(all[a] == e[a - 1]);
                } else {
                    assert(all[a] == e[a - 1] && all[b] == e[b - 1]);
                }
            }
        }
    }
}

/// An element of the list of elements is an element of the list.
pub proof fn lemma_elements_in(doc: Document, ch: Seq<NodeId>, p: NodeId)
    ensures
        i_elements(doc, ch).contains(p) <==> (ch.contains(p) && i_is_el(doc, p)),
    decreases ch.len(),
{
    if ch.len() > 0 {
        lemma_elements_in(doc, ch.drop_first(), p);
        let r = ch.drop_first();
        if i_is_el(doc, ch[0]) {
            let all = seq![ch[0]] + i_elements(doc, r);
            if i_elements(doc, r).contains(p) {
                let k = choose|k: int| 0 <= k < i_elements(doc, r).len() && i_elements(doc, r)[k] == p;
                assert(all[k + 1] == p);
                let kk = choose|kk: int| 0 <= kk < r.len() && r[kk] == p;
                assert(ch[kk + 1] == p);
            }
            if p == ch[0] {
                assert(all[0] == p);
            }
            if ch.contains(p) && i_is_el(doc, p) && p != ch[0] {
                let kk = choose|kk: int| 0 <= kk < ch.len() && ch[kk] == p;
                assert(kk > 0);
                assert(r[kk - 1] == p);
                let k = choose|k: int| 0 <= k < i_elements(doc, r).len() && i_elements(doc, r)[k] == p;
                assert(all[k + 1] == p);
            }
        } else {
            if ch.contains(p) && i_is_el(doc, p) {
                let kk = choose|kk: int| 0 <= kk < ch.len() && ch[kk] == p;
                assert(kk > 0);
                assert(r[kk - 1] == p);
            }
            if i_elements(doc, r).contains(p) {
                let kk = choose|kk: int| 0 <= kk < r.len() && r[kk] == p;
                assert(ch[kk + 1] == p);
            }
        }
    }
}

/// The first `cnt_el(j)` element children are the elements among the first `j` children.
pub proof fn lemma_elements_prefix(doc: Document, ch: Seq<NodeId>, j: int)
    requires
        0 <= j <= ch.len(),
    ensures
        i_elements(doc, ch).subrange(0, cnt_el(doc, ch, j)) == i_elements(doc, ch.subrange(0, j)),
{
    let pre = ch.subrange(0, j);
    let post = ch.subrange(j, ch.len() as int);
    assert(ch =~= pre + post);
    lemma_elements_append(doc, pre, post);
    assert(i_elements(doc, ch).subrange(0, cnt_el(doc, ch, j)) =~= i_elements(doc, pre));
}

// ------------------------------------------------------------------------------------
// Where an element is among its parent's children
// ------------------------------------------------------------------------------------

/// In a well-formed arena, an element with a parent is in the parent's children at the
/// index DOM gives, and among the parent's element children at the count of those before it.
pub proof fn lemma_position(doc: Document, x: NodeId)
    requires
        wf(doc),
        i_is_el(doc, x),
        parent(doc, x) is Some,
    ensures
        ({
            let par = parent(doc, x).unwrap();
            let ch = doc.nodes[par as int].children;
            let j = index_of(ch, x);
            &&& par < doc.nodes.len()
            &&& 0 <= j < ch.len()
            &&& ch[j] == x
            &&& ch.no_duplicates()
            &&& index_of(i_elements(doc, ch), x) == cnt_el(doc, ch, j)
            &&& i_elements(doc, ch)[cnt_el(doc, ch, j)] == x
            &&& 0 <= cnt_el(doc, ch, j) < i_elements(doc, ch).len()
        }),
{
    let paths = lemma_wf_witness(doc);
    let par = parent(doc, x).unwrap();
    let ch = doc.nodes[par as int].children;
    assert(par < doc.nodes.len());
    assert(ch.contains(x));
    assert(ch.no_duplicates());
    lemma_index_of(ch, x);
    let j = index_of(ch, x);
    lemma_elements_nth(doc, ch, j);
    lemma_elements_nodup(doc, ch);
    let e = i_elements(doc, ch);
    lemma_index_of_unique(e, cnt_el(doc, ch, j));
}

/// A node with the parent `par` is among its children.
pub proof fn lemma_child_of_parent(doc: Document, p: NodeId, par: NodeId)
    requires
        wf(doc),
        p < doc.nodes.len(),
        parent(doc, p) == Some(par),
    ensures
        par < doc.nodes.len(),
        doc.nodes[par as int].children.contains(p),
{
    let paths = lemma_wf_witness(doc);
}

// ------------------------------------------------------------------------------------
// Siblings: the spec scans the children, the transcription looks in the element list
// ------------------------------------------------------------------------------------

/// The spec's scan for the nearest earlier element that matches.
pub proof fn lemma_prev_elem(
    doc: Document,
    c: Complex,
    n: int,
    ch: Seq<NodeId>,
    k: int,
    q: spec_fn(NodeId) -> bool,
)
    requires
        0 <= k < ch.len(),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        previous_element_matches(doc, c, n, ch, k) == (cnt_el(doc, ch, k + 1) > 0 && q(
            i_elements(doc, ch)[cnt_el(doc, ch, k + 1) - 1],
        )),
    decreases k,
{
    reveal_with_fuel(previous_element_matches, 2);
    lemma_cnt_step(doc, ch, k);
    assert(is_element(doc, ch[k]) == i_is_el(doc, ch[k]));
    if i_is_el(doc, ch[k]) {
        lemma_elements_nth(doc, ch, k);
        assert(match_complex(doc, c, n, ch[k]) == q(ch[k]));
        assert(previous_element_matches(doc, c, n, ch, k) == match_complex(doc, c, n, ch[k]));
        assert(cnt_el(doc, ch, k + 1) == cnt_el(doc, ch, k) + 1);
        assert(i_elements(doc, ch)[cnt_el(doc, ch, k + 1) - 1] == ch[k]);
    } else {
        if k > 0 {
            lemma_prev_elem(doc, c, n, ch, k - 1, q);
            assert(previous_element_matches(doc, c, n, ch, k) == previous_element_matches(
                doc,
                c,
                n,
                ch,
                k - 1,
            ));
        } else {
            assert(ch.subrange(0, 0) =~= Seq::<NodeId>::empty());
            assert(cnt_el(doc, ch, 0) == 0);
            assert(previous_element_matches(doc, c, n, ch, k) == false);
        }
    }
}

/// The spec's scan over all earlier siblings.
pub proof fn lemma_earlier(
    doc: Document,
    c: Complex,
    n: int,
    ch: Seq<NodeId>,
    k: int,
    q: spec_fn(NodeId) -> bool,
)
    requires
        0 <= k < ch.len(),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        some_earlier_sibling_matches(doc, c, n, ch, k) == exists|k2: int|
            0 <= k2 <= k && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]),
    decreases k,
{
    reveal_with_fuel(some_earlier_sibling_matches, 2);
    assert(is_element(doc, ch[k]) == i_is_el(doc, ch[k]));
    if k > 0 {
        lemma_earlier(doc, c, n, ch, k - 1, q);
    }
    if i_is_el(doc, ch[k]) {
        assert(match_complex(doc, c, n, ch[k]) == q(ch[k]));
    }
    if exists|k2: int| 0 <= k2 <= k && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]) {
        let k2 = choose|k2: int| 0 <= k2 <= k && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]);
        if k2 < k {
            assert(0 <= k2 <= k - 1 && i_is_el(doc, ch[k2]) && q(ch[k2]));
        }
    }
    if k > 0 && some_earlier_sibling_matches(doc, c, n, ch, k - 1) {
        let k2 = choose|k2: int| 0 <= k2 <= k - 1 && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]);
        assert(0 <= k2 <= k && i_is_el(doc, ch[k2]) && q(ch[k2]));
    }
    assert(some_earlier_sibling_matches(doc, c, n, ch, k) == ((is_element(doc, ch[k]) && match_complex(
        doc,
        c,
        n,
        ch[k],
    )) || (k > 0 && some_earlier_sibling_matches(doc, c, n, ch, k - 1))));
}

/// What the transcription's next-sibling relation says, in terms of the element list.
pub proof fn lemma_related_next(doc: Document, p: NodeId, x: NodeId)
    requires
        wf(doc),
        i_is_el(doc, x),
        parent(doc, x) is Some,
    ensures
        ({
            let par = parent(doc, x).unwrap();
            let ch = doc.nodes[par as int].children;
            let e = i_elements(doc, ch);
            let i = cnt_el(doc, ch, index_of(ch, x));
            i_related(doc, IComb::Next, p, x) <==> (i > 0 && i_is_el(doc, p) && e[i - 1] == p)
        }),
{
    lemma_position(doc, x);
    let par = parent(doc, x).unwrap();
    let ch = doc.nodes[par as int].children;
    let e = i_elements(doc, ch);
    let i = cnt_el(doc, ch, index_of(ch, x));
    assert(i_sibs(doc, x) == e);
    assert(index_of(e, x) == i);
}

/// The next-sibling combinator: the spec's scan for the previous element is the
/// transcription's relation to the element before it in the element list.
pub proof fn lemma_next_sibling_iff(doc: Document, c: Complex, n: int, x: NodeId, q: spec_fn(NodeId) -> bool)
    requires
        wf(doc),
        is_element(doc, x),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        (match parent_of(doc, x) {
            Some(_) => previous_element_matches(
                doc,
                c,
                n,
                inclusive_siblings(doc, x),
                sibling_index(doc, x) - 1,
            ),
            None => false,
        }) == exists|p: NodeId| i_related(doc, IComb::Next, p, x) && #[trigger] q(p),
{
    match parent_of(doc, x) {
        None => {
            assert forall|p: NodeId| !i_related(doc, IComb::Next, p, x) by {}
        },
        Some(par) => {
            lemma_position(doc, x);
            let ch = doc.nodes[par as int].children;
            let j = index_of(ch, x);
            let e = i_elements(doc, ch);
            let i = cnt_el(doc, ch, j);
            assert(inclusive_siblings(doc, x) == ch);
            assert(sibling_index(doc, x) == j);
            if j > 0 {
                lemma_prev_elem(doc, c, n, ch, j - 1, q);
            } else {
                assert(ch.subrange(0, 0) =~= Seq::<NodeId>::empty());
                assert(i == 0);
            }
            assert forall|p: NodeId| i_related(doc, IComb::Next, p, x) implies i > 0 && p == e[i - 1] by {
                lemma_related_next(doc, p, x);
            }
            if i > 0 {
                lemma_elements_prefix(doc, ch, j);
                lemma_elements_in(doc, ch, e[i - 1]);
                lemma_related_next(doc, e[i - 1], x);
                assert(i_related(doc, IComb::Next, e[i - 1], x));
            }
        },
    }
}

/// The subsequent-sibling combinator.
pub proof fn lemma_subsequent_iff(doc: Document, c: Complex, n: int, x: NodeId, q: spec_fn(NodeId) -> bool)
    requires
        wf(doc),
        is_element(doc, x),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        (match parent_of(doc, x) {
            Some(_) => some_earlier_sibling_matches(
                doc,
                c,
                n,
                inclusive_siblings(doc, x),
                sibling_index(doc, x) - 1,
            ),
            None => false,
        }) == exists|p: NodeId| i_related(doc, IComb::Subsequent, p, x) && #[trigger] q(p),
{
    reveal_with_fuel(some_earlier_sibling_matches, 2);
    match parent_of(doc, x) {
        None => {
            assert forall|p: NodeId| !i_related(doc, IComb::Subsequent, p, x) by {}
        },
        Some(par) => {
            lemma_position(doc, x);
            let ch = doc.nodes[par as int].children;
            let j = index_of(ch, x);
            let e = i_elements(doc, ch);
            let i = cnt_el(doc, ch, j);
            assert(inclusive_siblings(doc, x) == ch);
            assert(sibling_index(doc, x) == j);
            assert(i_sibs(doc, x) == e);
            if j > 0 {
                lemma_earlier(doc, c, n, ch, j - 1, q);
            }
            // (spec => transcription)
            if exists|k2: int| 0 <= k2 <= j - 1 && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]) {
                let k2 = choose|k2: int| 0 <= k2 <= j - 1 && i_is_el(doc, #[trigger] ch[k2]) && q(ch[k2]);
                let p = ch[k2];
                lemma_index_of_unique(ch, k2);
                lemma_position(doc, p);
                lemma_cnt_step(doc, ch, k2);
                lemma_cnt_mono(doc, ch, k2 + 1, j);
                assert(parent(doc, p) == Some(par));
                assert(i_related(doc, IComb::Subsequent, p, x));
            }
            // (transcription => spec)
            if exists|p: NodeId| i_related(doc, IComb::Subsequent, p, x) && #[trigger] q(p) {
                let p = choose|p: NodeId| i_related(doc, IComb::Subsequent, p, x) && #[trigger] q(p);
                assert(parent(doc, p) == Some(par));
                lemma_position(doc, p);
                let jp = index_of(ch, p);
                if jp >= j {
                    lemma_cnt_mono(doc, ch, j, jp);
                }
                assert(jp <= j - 1);
                assert(i_is_el(doc, ch[jp]) && q(ch[jp]));
            }
        },
    }
}

/// The child combinator.
pub proof fn lemma_child_iff(doc: Document, c: Complex, n: int, x: NodeId, q: spec_fn(NodeId) -> bool)
    requires
        is_element(doc, x),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        (match parent_of(doc, x) {
            Some(p) => is_element(doc, p) && match_complex(doc, c, n, p),
            None => false,
        }) == exists|p: NodeId| i_related(doc, IComb::Child, p, x) && #[trigger] q(p),
{
    match parent_of(doc, x) {
        None => {
            assert forall|p: NodeId| !i_related(doc, IComb::Child, p, x) by {}
        },
        Some(par) => {
            assert(parent(doc, x) == Some(par));
            if is_element(doc, par) {
                assert(match_complex(doc, c, n, par) == q(par));
                assert(i_related(doc, IComb::Child, par, x));
            }
        },
    }
}

// ------------------------------------------------------------------------------------
// Ancestors
// ------------------------------------------------------------------------------------

/// What following parents from `x` can reach is on `x`'s path.
pub proof fn lemma_within_in_path(doc: Document, paths: Seq<Seq<NodeId>>, a: NodeId, x: NodeId, fuel: nat)
    requires
        wf_with(doc, paths),
        x < doc.nodes.len(),
        inclusive_ancestor_within(doc, a, x, fuel),
    ensures
        paths[x as int].contains(a),
    decreases fuel,
{
    lemma_path(doc, paths, x);
    let px = paths[x as int];
    if x == a {
        assert(px[px.len() - 1] == a);
    } else {
        match doc.nodes[x as int].parent {
            None => {},
            Some(p) => {
                assert(p < doc.nodes.len());
                lemma_within_in_path(doc, paths, a, p, (fuel - 1) as nat);
                let k = choose|k: int| 0 <= k < paths[p as int].len() && paths[p as int][k] == a;
                assert(px[k] == a);
            },
        }
    }
}

/// In a well-formed arena no node is among its own parent's ancestors.
pub proof fn lemma_no_cycle(doc: Document, x: NodeId, q: NodeId, fuel: nat)
    requires
        wf(doc),
        x < doc.nodes.len(),
        parent(doc, x) == Some(q),
    ensures
        !inclusive_ancestor_within(doc, x, q, fuel),
{
    let paths = lemma_wf_witness(doc);
    assert(q < doc.nodes.len());
    if inclusive_ancestor_within(doc, x, q, fuel) {
        lemma_within_in_path(doc, paths, x, q, fuel);
        lemma_path_facts(doc, paths, x);
        let px = paths[x as int];
        let k = choose|k: int| 0 <= k < paths[q as int].len() && paths[q as int][k] == x;
        assert(px[k] == x);
        assert(px[px.len() - 1] == x);
        assert(k != px.len() - 1);
    }
}

/// An element is among `a` and the `f - 1` ancestors above it, and `q` holds of it.
pub open spec fn rhs_walk(doc: Document, a: NodeId, f: nat, q: spec_fn(NodeId) -> bool) -> bool {
    f >= 1 && exists|p: NodeId|
        inclusive_ancestor_within(doc, p, a, (f - 1) as nat) && is_element(doc, p) && #[trigger] q(p)
}

/// [`rhs_walk`] one step up.
pub proof fn lemma_rhs_step(doc: Document, a: NodeId, f: nat, q: spec_fn(NodeId) -> bool)
    requires
        f >= 1,
    ensures
        rhs_walk(doc, a, f, q) == ((is_element(doc, a) && q(a)) || (match doc.nodes[a as int].parent {
            Some(par) => rhs_walk(doc, par, (f - 1) as nat, q),
            None => false,
        })),
{
    if rhs_walk(doc, a, f, q) {
        let p = choose|p: NodeId|
            inclusive_ancestor_within(doc, p, a, (f - 1) as nat) && is_element(doc, p) && #[trigger] q(p);
        if p != a {
            match doc.nodes[a as int].parent {
                Some(par) => {
                    assert(inclusive_ancestor_within(doc, p, par, (f - 2) as nat));
                },
                None => {},
            }
        }
    }
    if is_element(doc, a) && q(a) {
        assert(inclusive_ancestor_within(doc, a, a, (f - 1) as nat));
    }
    match doc.nodes[a as int].parent {
        Some(par) => {
            if rhs_walk(doc, par, (f - 1) as nat, q) {
                let p = choose|p: NodeId|
                    inclusive_ancestor_within(doc, p, par, (f - 2) as nat) && is_element(doc, p) && #[trigger] q(p);
                assert(inclusive_ancestor_within(doc, p, a, (f - 1) as nat));
            }
        },
        None => {},
    }
}

/// The spec's walk up the parents, from `a` with `f` steps left, finds a matching element
/// exactly when one is among `a` and the `f - 1` ancestors above it.
pub proof fn lemma_walk_iff(
    doc: Document,
    c: Complex,
    n: int,
    a: NodeId,
    f: nat,
    q: spec_fn(NodeId) -> bool,
)
    requires
        wf(doc),
        a < doc.nodes.len(),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        some_ancestor_matches(doc, c, n, Some(a), f) == rhs_walk(doc, a, f, q),
    decreases f,
{
    if f >= 1 {
        let _ = lemma_wf_witness(doc);
        lemma_rhs_step(doc, a, f, q);
        if is_element(doc, a) {
            assert(match_complex(doc, c, n, a) == q(a));
        }
        assert(parent_of(doc, a) == doc.nodes[a as int].parent);
        assert(some_ancestor_matches(doc, c, n, Some(a), f) == ((is_element(doc, a) && match_complex(
            doc,
            c,
            n,
            a,
        )) || some_ancestor_matches(doc, c, n, parent_of(doc, a), (f - 1) as nat)));
        match parent_of(doc, a) {
            None => {
                assert(some_ancestor_matches(doc, c, n, None, (f - 1) as nat) == false);
            },
            Some(par) => {
                assert(par < doc.nodes.len());
                lemma_walk_iff(doc, c, n, par, (f - 1) as nat, q);
            },
        }
    }
}


/// The descendant combinator.
pub proof fn lemma_descendant_iff(doc: Document, c: Complex, n: int, x: NodeId, q: spec_fn(NodeId) -> bool)
    requires
        wf(doc),
        is_element(doc, x),
        forall|y: NodeId| is_element(doc, y) ==> match_complex(doc, c, n, y) == #[trigger] q(y),
    ensures
        some_ancestor_matches(doc, c, n, parent_of(doc, x), doc.nodes.len())
            == exists|p: NodeId| i_related(doc, IComb::Descendant, p, x) && #[trigger] q(p),
{
    let len = doc.nodes.len();
    let _ = lemma_wf_witness(doc);
    match parent_of(doc, x) {
        None => {
            assert forall|p: NodeId| !i_related(doc, IComb::Descendant, p, x) by {
                if i_related(doc, IComb::Descendant, p, x) {
                    assert(inclusive_ancestor_within(doc, p, x, len));
                }
            }
        },
        Some(par) => {
            assert(par < len);
            lemma_walk_iff(doc, c, n, par, len, q);
            // spec => transcription
            if some_ancestor_matches(doc, c, n, Some(par), len) {
                let p = choose|p: NodeId|
                    inclusive_ancestor_within(doc, p, par, (len - 1) as nat) && is_element(doc, p) && #[trigger] q(p);
                lemma_no_cycle(doc, x, par, (len - 1) as nat);
                assert(p != x);
                assert(inclusive_ancestor_within(doc, p, x, len));
                assert(i_related(doc, IComb::Descendant, p, x));
            }
            // transcription => spec
            if exists|p: NodeId| i_related(doc, IComb::Descendant, p, x) && #[trigger] q(p) {
                let p = choose|p: NodeId| i_related(doc, IComb::Descendant, p, x) && #[trigger] q(p);
                assert(is_descendant(doc, x, p));
                assert(inclusive_ancestor_within(doc, p, x, len));
                assert(p != x);
                assert(inclusive_ancestor_within(doc, p, par, (len - 1) as nat));
            }
        },
    }
}

// ------------------------------------------------------------------------------------
// Positions among the siblings
// ------------------------------------------------------------------------------------

/// Without an `of`, the transcription counts every element in the range.
pub proof fn lemma_cnt_free(
    doc: Document,
    scope: Option<NodeId>,
    of: Seq<IComplex>,
    sibs: Seq<NodeId>,
    lo: int,
    hi: int,
)
    ensures
        i_cnt(doc, scope, false, of, sibs, lo, hi) == if hi > lo {
            hi - lo
        } else {
            0int
        },
    decreases hi - lo,
{
    if lo < hi {
        lemma_cnt_free(doc, scope, of, sibs, lo, hi - 1);
    }
}

/// The spec's count of the elements before child `j`, when every element counts.
pub proof fn lemma_count_before_free(doc: Document, x: NodeId, ch: Seq<NodeId>, j: int)
    requires
        0 <= j <= ch.len(),
    ensures
        count_before(doc, x, ch, j, false) == cnt_el(doc, ch, j),
    decreases j,
{
    if j == 0 {
        assert(ch.subrange(0, 0) =~= Seq::<NodeId>::empty());
    } else {
        lemma_count_before_free(doc, x, ch, j - 1);
        lemma_cnt_step(doc, ch, j - 1);
    }
}

/// The spec's count of the elements from child `j` on, when every element counts.
pub proof fn lemma_count_from_free(doc: Document, x: NodeId, ch: Seq<NodeId>, j: int)
    requires
        0 <= j <= ch.len(),
    ensures
        count_from(doc, x, ch, j, false) == i_elements(doc, ch).len() - cnt_el(doc, ch, j),
    decreases ch.len() - j,
{
    if j == ch.len() {
        lemma_cnt_all(doc, ch);
    } else {
        lemma_count_from_free(doc, x, ch, j + 1);
        lemma_cnt_step(doc, ch, j);
    }
}

/// The transcription's count of the elements of `x`'s type in a range splits at any point.
pub proof fn lemma_cnt_type_split(doc: Document, sibs: Seq<NodeId>, x: NodeId, lo: int, mid: int, hi: int)
    requires
        lo <= mid <= hi,
    ensures
        i_cnt_type(doc, sibs, x, lo, hi) == i_cnt_type(doc, sibs, x, lo, mid) + i_cnt_type(doc, sibs, x, mid, hi),
    decreases hi - mid,
{
    if mid < hi {
        lemma_cnt_type_split(doc, sibs, x, lo, mid, hi - 1);
    }
}

/// The transcription's count of one more element at the front of a range.
pub proof fn lemma_cnt_type_front(doc: Document, sibs: Seq<NodeId>, x: NodeId, lo: int, hi: int)
    requires
        lo < hi,
    ensures
        i_cnt_type(doc, sibs, x, lo, hi) == (if i_ns(doc, sibs[lo]) == i_ns(doc, x) && i_local(doc, sibs[lo])
            == i_local(doc, x) {
            1int
        } else {
            0int
        }) + i_cnt_type(doc, sibs, x, lo + 1, hi),
{
    lemma_cnt_type_split(doc, sibs, x, lo, lo + 1, hi);
    assert(i_cnt_type(doc, sibs, x, lo, lo) == 0);
    assert(i_cnt_type(doc, sibs, x, lo, lo + 1) == (if i_ns(doc, sibs[lo]) == i_ns(doc, x) && i_local(
        doc,
        sibs[lo],
    ) == i_local(doc, x) {
        1int
    } else {
        0int
    }));
}

/// The transcription's count of the elements of a type is not negative.
pub proof fn lemma_cnt_type_nonneg(doc: Document, sibs: Seq<NodeId>, x: NodeId, lo: int, hi: int)
    ensures
        i_cnt_type(doc, sibs, x, lo, hi) >= 0,
        i_cnt_type(doc, sibs, x, lo, hi) <= if hi > lo {
            hi - lo
        } else {
            0int
        },
    decreases hi - lo,
{
    if lo < hi {
        lemma_cnt_type_nonneg(doc, sibs, x, lo, hi - 1);
    }
}

/// The spec's count of earlier siblings of the same type, with the element list.
pub proof fn lemma_count_before_type(doc: Document, x: NodeId, ch: Seq<NodeId>, j: int)
    requires
        0 <= j <= ch.len(),
    ensures
        count_before(doc, x, ch, j, true) == i_cnt_type(doc, i_elements(doc, ch), x, 0, cnt_el(doc, ch, j)),
    decreases j,
{
    if j == 0 {
        assert(ch.subrange(0, 0) =~= Seq::<NodeId>::empty());
    } else {
        lemma_count_before_type(doc, x, ch, j - 1);
        lemma_cnt_step(doc, ch, j - 1);
        if i_is_el(doc, ch[j - 1]) {
            lemma_elements_nth(doc, ch, j - 1);
            assert(i_elements(doc, ch)[cnt_el(doc, ch, j - 1)] == ch[j - 1]);
        }
    }
}

/// The spec's count of later siblings of the same type, with the element list.
pub proof fn lemma_count_from_type(doc: Document, x: NodeId, ch: Seq<NodeId>, j: int)
    requires
        0 <= j <= ch.len(),
    ensures
        count_from(doc, x, ch, j, true) == i_cnt_type(
            doc,
            i_elements(doc, ch),
            x,
            cnt_el(doc, ch, j),
            i_elements(doc, ch).len() as int,
        ),
    decreases ch.len() - j,
{
    if j == ch.len() {
        lemma_cnt_all(doc, ch);
    } else {
        lemma_count_from_type(doc, x, ch, j + 1);
        lemma_cnt_step(doc, ch, j);
        if i_is_el(doc, ch[j]) {
            lemma_elements_nth(doc, ch, j);
            lemma_cnt_type_front(
                doc,
                i_elements(doc, ch),
                x,
                cnt_el(doc, ch, j),
                i_elements(doc, ch).len() as int,
            );
        }
    }
}

/// An element's 1-based position among its siblings, as the spec counts it, is one more than
/// the transcription's count of what is before it (or after it).
pub proof fn lemma_child_index(doc: Document, x: NodeId, of_type: bool, from_end: bool)
    requires
        wf(doc),
        is_element(doc, x),
    ensures
        ({
            let sibs = i_sibs(doc, x);
            let i = index_of(sibs, x);
            &&& 0 <= i < sibs.len()
            &&& child_index(doc, x, of_type, from_end) == 1 + if of_type {
                if from_end {
                    i_cnt_type(doc, sibs, x, i + 1, sibs.len() as int)
                } else {
                    i_cnt_type(doc, sibs, x, 0, i)
                }
            } else {
                if from_end {
                    sibs.len() - (i + 1)
                } else {
                    i
                }
            }
        }),
{
    match parent_of(doc, x) {
        None => {
            assert(parent(doc, x) is None);
            assert(i_sibs(doc, x) == seq![x]);
            assert(inclusive_siblings(doc, x) == seq![x]);
            assert(index_of(seq![x], x) == 0);
            assert(sibling_index(doc, x) == 0);
            assert(i_cnt_type(doc, seq![x], x, 0, 0) == 0);
            assert(i_cnt_type(doc, seq![x], x, 1, 1) == 0);
        },
        Some(par) => {
            lemma_position(doc, x);
            let ch = doc.nodes[par as int].children;
            let j = index_of(ch, x);
            let e = i_elements(doc, ch);
            assert(i_sibs(doc, x) == e);
            assert(inclusive_siblings(doc, x) == ch);
            assert(sibling_index(doc, x) == j);
            lemma_count_before_free(doc, x, ch, j);
            lemma_count_before_type(doc, x, ch, j);
            lemma_cnt_step(doc, ch, j);
            lemma_count_from_free(doc, x, ch, j + 1);
            lemma_count_from_type(doc, x, ch, j + 1);
        },
    }
}

// ------------------------------------------------------------------------------------
// Child-indexed pseudo-classes
// ------------------------------------------------------------------------------------

/// `An + B` with `A = 0` and `B = 1` is the index 1.
pub proof fn lemma_anb_first(pos: int)
    ensures
        i_anb(0, 1, pos) == (pos == 1),
{
    if pos == 1 {
        assert(0 * 0 + 1 == pos);
    }
}

/// An element's position as the transcription counts it, from the spec's `child_index`.
pub proof fn lemma_nth_child_same(doc: Document, scope: Option<NodeId>, x: NodeId, a: int, b: int, last: bool, of: Seq<IComplex>)
    requires
        wf(doc),
        is_element(doc, x),
    ensures
        nth_index_matches(a, b, child_index(doc, x, false, last)) == i_m_simple(
            doc,
            scope,
            ISimple::NthChild { a, b, last, has_of: false, of },
            x,
        ),
{
    lemma_child_index(doc, x, false, last);
    let sibs = i_sibs(doc, x);
    let i = index_of(sibs, x);
    lemma_nth_index_matches(a, b, child_index(doc, x, false, last));
    lemma_cnt_free(doc, scope, of, sibs, i + 1, sibs.len() as int);
    lemma_cnt_free(doc, scope, of, sibs, 0, i);
}

/// The same for the type-indexed ones.
pub proof fn lemma_nth_type_same(doc: Document, scope: Option<NodeId>, x: NodeId, a: int, b: int, last: bool)
    requires
        wf(doc),
        is_element(doc, x),
    ensures
        nth_index_matches(a, b, child_index(doc, x, true, last)) == i_m_simple(
            doc,
            scope,
            ISimple::NthType { a, b, last },
            x,
        ),
{
    lemma_child_index(doc, x, true, last);
    lemma_nth_index_matches(a, b, child_index(doc, x, true, last));
}

/// `:only-of-type`.
pub proof fn lemma_only_of_type_same(doc: Document, scope: Option<NodeId>, x: NodeId)
    requires
        wf(doc),
        is_element(doc, x),
    ensures
        (child_index(doc, x, true, false) == 1 && child_index(doc, x, true, true) == 1) == i_m_simple(
            doc,
            scope,
            ISimple::OnlyOfType,
            x,
        ),
{
    lemma_child_index(doc, x, true, false);
    lemma_child_index(doc, x, true, true);
    let sibs = i_sibs(doc, x);
    let i = index_of(sibs, x);
    lemma_cnt_type_split(doc, sibs, x, 0, i, sibs.len() as int);
    lemma_cnt_type_split(doc, sibs, x, i, i + 1, sibs.len() as int);
    lemma_cnt_type_nonneg(doc, sibs, x, 0, i);
    lemma_cnt_type_nonneg(doc, sibs, x, i + 1, sibs.len() as int);
    // `x` is of its own type.
    lemma_index_of(sibs, x);
    assert(sibs[i] == x);
    lemma_cnt_type_front(doc, sibs, x, i, i + 1);
    assert(i_cnt_type(doc, sibs, x, i + 1, i + 1) == 0);
}

/// `:only-child`.
pub proof fn lemma_only_child_same(doc: Document, scope: Option<NodeId>, x: NodeId)
    requires
        wf(doc),
        is_element(doc, x),
    ensures
        (child_index(doc, x, false, false) == 1 && child_index(doc, x, false, true) == 1) == i_m_simple(
            doc,
            scope,
            ISimple::OnlyChild,
            x,
        ),
{
    lemma_child_index(doc, x, false, false);
    lemma_child_index(doc, x, false, true);
}

// ------------------------------------------------------------------------------------
// Matching, by induction on the selector
// ------------------------------------------------------------------------------------

/// A well-formed arena is not empty.
pub proof fn lemma_wf_nonempty(doc: Document)
    requires
        wf(doc),
    ensures
        doc.nodes.len() > 0,
{
    let _ = lemma_wf_witness(doc);
}

/// A related simple selector matches an element as its transcription does.
pub proof fn lemma_match_simple(doc: Document, scope: Option<NodeId>, s: Simple, m: ISimple, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_simple(s, m),
        is_element(doc, x),
    ensures
        simple_matches(doc, s, x) == i_m_simple(doc, scope, m, x),
    decreases s, 0nat, 0int,
{
    lemma_wf_nonempty(doc);
    match s {
        Simple::Id { name } => lemma_id_same(doc, x, name),
        Simple::Class { name } => lemma_class_same(doc, x, name),
        Simple::Attribute { ns, name, test } => {
            match m {
                ISimple::Attr(a) => lemma_attribute_same(doc, x, ns, name, test, a),
                _ => {},
            }
        },
        Simple::PseudoClass { class } => {
            match class {
                PseudoClass::Empty => lemma_empty_same(doc, x),
                PseudoClass::FirstChild => {
                    lemma_nth_child_same(doc, scope, x, 0, 1, false, Seq::empty());
                    lemma_nth_index_matches(0, 1, child_index(doc, x, false, false));
                    lemma_anb_first(child_index(doc, x, false, false));
                },
                PseudoClass::LastChild => {
                    lemma_nth_child_same(doc, scope, x, 0, 1, true, Seq::empty());
                    lemma_nth_index_matches(0, 1, child_index(doc, x, false, true));
                    lemma_anb_first(child_index(doc, x, false, true));
                },
                PseudoClass::OnlyChild => lemma_only_child_same(doc, scope, x),
                PseudoClass::FirstOfType => {
                    lemma_nth_type_same(doc, scope, x, 0, 1, false);
                    lemma_nth_index_matches(0, 1, child_index(doc, x, true, false));
                    lemma_anb_first(child_index(doc, x, true, false));
                },
                PseudoClass::LastOfType => {
                    lemma_nth_type_same(doc, scope, x, 0, 1, true);
                    lemma_nth_index_matches(0, 1, child_index(doc, x, true, true));
                    lemma_anb_first(child_index(doc, x, true, true));
                },
                PseudoClass::OnlyOfType => lemma_only_of_type_same(doc, scope, x),
                _ => {},
            }
        },
        Simple::Nth { kind, a, b } => {
            match kind {
                NthKind::Child => lemma_nth_child_same(doc, scope, x, a, b, false, Seq::empty()),
                NthKind::LastChild => lemma_nth_child_same(doc, scope, x, a, b, true, Seq::empty()),
                NthKind::OfType => lemma_nth_type_same(doc, scope, x, a, b, false),
                NthKind::LastOfType => lemma_nth_type_same(doc, scope, x, a, b, true),
            }
        },
        Simple::Is { arg } => {
            match m {
                ISimple::Is(l) => lemma_match_list(doc, scope, arg, l, x),
                _ => {},
            }
        },
        Simple::Where { arg } => {
            match m {
                ISimple::Where(l) => lemma_match_list(doc, scope, arg, l, x),
                _ => {},
            }
        },
        Simple::Not { arg } => {
            match m {
                ISimple::Not(l) => lemma_match_list(doc, scope, arg, l, x),
                _ => {},
            }
        },
        _ => {},
    }
}

/// The spec's check of the first `k` simple selectors is the quantifier over them.
pub proof fn lemma_compound_prefix(doc: Document, c: Seq<Simple>, k: int, x: NodeId)
    requires
        0 <= k <= c.len(),
    ensures
        compound_matches(doc, c, k, x) == forall|j: int| 0 <= j < k ==> simple_matches(doc, #[trigger] c[j], x),
    decreases k,
{
    if k > 0 {
        lemma_compound_prefix(doc, c, k - 1, x);
    }
}

/// A related compound selector matches an element as its transcription does.
pub proof fn lemma_match_compound(doc: Document, scope: Option<NodeId>, c: Seq<Simple>, m: ICompound, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_compound(c, m),
        c.len() > 0,
    ensures
        compound_matches(doc, c, c.len() as int, x) == i_m_compound(doc, scope, m, x),
    decreases c, 1nat, 0int,
{
    let off = comp_off(c);
    lemma_compound_prefix(doc, c, c.len() as int, x);
    if is_element(doc, x) {
        assert forall|j: int| 0 <= j < m.subs.len() implies simple_matches(doc, c[off + j], x) == i_m_simple(
            doc,
            scope,
            m.subs[j],
            x,
        ) by {
            lemma_match_simple(doc, scope, c[off + j], m.subs[j], x);
        }
        match m.ty {
            Some(t) => {
                lemma_type_same(doc, x, c[0], t);
            },
            None => {},
        }
        // Each side's quantifier is the other's.
        if i_m_compound(doc, scope, m, x) {
            assert forall|j: int| 0 <= j < c.len() implies simple_matches(doc, #[trigger] c[j], x) by {
                if j >= off {
                    assert(simple_matches(doc, c[off + (j - off)], x));
                }
            }
        }
        if compound_matches(doc, c, c.len() as int, x) {
            assert forall|k: int| 0 <= k < m.subs.len() implies i_m_simple(doc, scope, #[trigger] m.subs[k], x) by {
                assert(simple_matches(doc, c[off + k], x));
            }
        }
    } else {
        assert(!simple_matches(doc, c[0], x));
    }
}

/// The spec's search along a combinator, from `x`, for a complex selector's first `n1` compound
/// selectors.
pub open spec fn spec_search(doc: Document, c: Complex, n1: int, x: NodeId, cs: Combinator) -> bool {
    match cs {
        Combinator::Descendant => some_ancestor_matches(doc, c, n1, parent_of(doc, x), doc.nodes.len()),
        Combinator::Child => match parent_of(doc, x) {
            Some(p) => is_element(doc, p) && match_complex(doc, c, n1, p),
            None => false,
        },
        Combinator::NextSibling => previous_element_matches(
            doc,
            c,
            n1,
            inclusive_siblings(doc, x),
            sibling_index(doc, x) - 1,
        ),
        Combinator::SubsequentSibling => some_earlier_sibling_matches(
            doc,
            c,
            n1,
            inclusive_siblings(doc, x),
            sibling_index(doc, x) - 1,
        ),
    }
}

/// One step of "match a complex selector": the spec's search along a combinator is the
/// transcription's quantifier, given what is known of the compound selectors to the left.
pub proof fn lemma_comb_step(
    doc: Document,
    scope: Option<NodeId>,
    c: Complex,
    m: IComplex,
    n: int,
    x: NodeId,
    cs: Combinator,
    cm: IComb,
)
    requires
        wf(doc),
        is_element(doc, x),
        n >= 2,
        rel_comb(cs, cm),
        forall|y: NodeId|
            is_element(doc, y) ==> #[trigger] match_complex(doc, c, n - 1, y) == i_m_at(
                doc,
                scope,
                m,
                None,
                n - 2,
                y,
            ),
    ensures
        spec_search(doc, c, n - 1, x, cs) == exists|p: NodeId|
            #[trigger] i_related(doc, cm, p, x) && i_m_at(doc, scope, m, None, n - 2, p),
{
    let q = |y: NodeId| i_m_at(doc, scope, m, None, n - 2, y);
    assert forall|y: NodeId| is_element(doc, y) implies match_complex(doc, c, n - 1, y) == #[trigger] q(y) by {
        assert(q(y) == i_m_at(doc, scope, m, None, n - 2, y));
    }
    match cs {
        Combinator::Descendant => lemma_descendant_iff(doc, c, n - 1, x, q),
        Combinator::Child => lemma_child_iff(doc, c, n - 1, x, q),
        Combinator::NextSibling => {
            lemma_next_sibling_iff(doc, c, n - 1, x, q);
            if parent_of(doc, x) is None {
                assert(previous_element_matches(doc, c, n - 1, inclusive_siblings(doc, x), sibling_index(doc, x) - 1) == false);
            }
        },
        Combinator::SubsequentSibling => {
            lemma_subsequent_iff(doc, c, n - 1, x, q);
            if parent_of(doc, x) is None {
                assert(some_earlier_sibling_matches(doc, c, n - 1, inclusive_siblings(doc, x), sibling_index(doc, x) - 1) == false);
            }
        },
    }
    // The closure's application is the body.
    if exists|p: NodeId| i_related(doc, cm, p, x) && #[trigger] q(p) {
        let p = choose|p: NodeId| i_related(doc, cm, p, x) && #[trigger] q(p);
        assert(i_m_at(doc, scope, m, None, n - 2, p));
    }
    if exists|p: NodeId| #[trigger] i_related(doc, cm, p, x) && i_m_at(doc, scope, m, None, n - 2, p) {
        let p = choose|p: NodeId| #[trigger] i_related(doc, cm, p, x) && i_m_at(doc, scope, m, None, n - 2, p);
        assert(q(p));
    }
}

/// The first compound selector alone.
pub proof fn lemma_complex_first(doc: Document, scope: Option<NodeId>, c: Complex, m: IComplex, x: NodeId)
    requires
        rel_complex(c, m),
        compound_matches(doc, c.compounds[0], c.compounds[0].len() as int, x) == i_m_compound(
            doc,
            scope,
            m.units[0],
            x,
        ),
    ensures
        match_complex(doc, c, 1, x) == i_m_at(doc, scope, m, None, 0, x),
{
    assert(m.units.len() == c.compounds.len());
    assert(m.lead is None);
    assert(c.compounds.len() >= 1);
    reveal_with_fuel(i_m_at, 2);
    reveal_with_fuel(match_complex, 2);
}

/// A later compound selector, when `x` is not an element.
pub proof fn lemma_complex_not_element(doc: Document, scope: Option<NodeId>, c: Complex, m: IComplex, n: int, x: NodeId)
    requires
        rel_complex(c, m),
        1 <= n <= c.compounds.len(),
        !is_element(doc, x),
        compound_matches(doc, c.compounds[n - 1], c.compounds[n - 1].len() as int, x) == i_m_compound(
            doc,
            scope,
            m.units[n - 1],
            x,
        ),
    ensures
        match_complex(doc, c, n, x) == i_m_at(doc, scope, m, None, n - 1, x),
{
    assert(m.units.len() == c.compounds.len());
    assert(is_element(doc, x) == i_is_el(doc, x));
    assert(!i_m_compound(doc, scope, m.units[n - 1], x));
    reveal_with_fuel(i_m_at, 2);
    reveal_with_fuel(match_complex, 2);
}

/// A later compound selector, when `x` is an element: the unfolding of both sides.
pub proof fn lemma_complex_later(doc: Document, scope: Option<NodeId>, c: Complex, m: IComplex, n: int, x: NodeId)
    requires
        rel_complex(c, m),
        2 <= n <= c.compounds.len(),
        compound_matches(doc, c.compounds[n - 1], c.compounds[n - 1].len() as int, x) == i_m_compound(
            doc,
            scope,
            m.units[n - 1],
            x,
        ),
        spec_search(doc, c, n - 1, x, c.combinators[n - 2]) == exists|p: NodeId|
            #[trigger] i_related(doc, m.combs[n - 2], p, x) && i_m_at(doc, scope, m, None, n - 2, p),
    ensures
        match_complex(doc, c, n, x) == i_m_at(doc, scope, m, None, n - 1, x),
{
    assert(m.units.len() == c.compounds.len());
    assert(m.lead is None);
    assert(c.combinators.len() + 1 == c.compounds.len());
    reveal_with_fuel(i_m_at, 2);
    reveal_with_fuel(match_complex, 2);
    let ex = exists|p: NodeId|
        #[trigger] i_related(doc, m.combs[n - 2], p, x) && i_m_at(doc, scope, m, None, n - 2, p);
    if ex {
        let p = choose|p: NodeId|
            #[trigger] i_related(doc, m.combs[n - 2], p, x) && i_m_at(doc, scope, m, None, n - 2, p);
        assert(i_related(doc, m.combs[n - 2], p, x));
        assert(i_m_at(doc, scope, m, None, n - 2, p));
    }
    assert(i_m_at(doc, scope, m, None, n - 1, x) ==> ex);
    assert(match_complex(doc, c, n, x) == (compound_matches(
        doc,
        c.compounds[n - 1],
        c.compounds[n - 1].len() as int,
        x,
    ) && spec_search(doc, c, n - 1, x, c.combinators[n - 2])));
}

/// One step of [`lemma_match_complex`], given what the induction knows.
pub proof fn lemma_complex_step(doc: Document, scope: Option<NodeId>, c: Complex, m: IComplex, n: int, x: NodeId)
    requires
        wf(doc),
        rel_complex(c, m),
        1 <= n <= c.compounds.len(),
        compound_matches(doc, c.compounds[n - 1], c.compounds[n - 1].len() as int, x) == i_m_compound(
            doc,
            scope,
            m.units[n - 1],
            x,
        ),
        n >= 2 ==> forall|y: NodeId|
            is_element(doc, y) ==> #[trigger] match_complex(doc, c, n - 1, y) == i_m_at(
                doc,
                scope,
                m,
                None,
                n - 2,
                y,
            ),
    ensures
        match_complex(doc, c, n, x) == i_m_at(doc, scope, m, None, n - 1, x),
{
    if !is_element(doc, x) {
        lemma_complex_not_element(doc, scope, c, m, n, x);
    } else if n == 1 {
        lemma_complex_first(doc, scope, c, m, x);
    } else {
        assert(rel_comb(c.combinators[n - 2], m.combs[n - 2]));
        assert(c.combinators.len() + 1 == c.compounds.len());
        lemma_comb_step(doc, scope, c, m, n, x, c.combinators[n - 2], m.combs[n - 2]);
        lemma_complex_later(doc, scope, c, m, n, x);
    }
}

/// A related complex selector matches an element as its transcription does, on the first `n`
/// compound selectors.
pub proof fn lemma_match_complex(doc: Document, scope: Option<NodeId>, c: Complex, m: IComplex, n: int, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_complex(c, m),
        1 <= n <= c.compounds.len(),
    ensures
        match_complex(doc, c, n, x) == i_m_at(doc, scope, m, None, n - 1, x),
    decreases c, 2nat, n,
{
    assert(rel_compound(c.compounds[n - 1], m.units[n - 1]));
    assert(c.compounds[n - 1].len() > 0);
    lemma_match_compound(doc, scope, c.compounds[n - 1], m.units[n - 1], x);
    if n >= 2 {
        assert forall|y: NodeId|
            is_element(doc, y) implies #[trigger] match_complex(doc, c, n - 1, y) == i_m_at(
            doc,
            scope,
            m,
            None,
            n - 2,
            y,
        ) by {
            lemma_match_complex(doc, scope, c, m, n - 1, y);
        }
    }
    lemma_complex_step(doc, scope, c, m, n, x);
}

/// A related selector list matches an element as its transcription does.
pub proof fn lemma_match_list(doc: Document, scope: Option<NodeId>, l: Seq<Complex>, m: Seq<IComplex>, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_list(l, m),
    ensures
        match_list(doc, l, l.len() as int, x) == i_m_list(doc, scope, m, x),
    decreases l, 4nat, 0int,
{
    assert(l.len() == m.len());
    lemma_match_list_prefix(doc, scope, l, m, m.len() as int, x);
    lemma_i_m_list_exists(doc, scope, m, x);
}

/// The transcription's `i_m_list` is the quantifier over its selectors.
pub proof fn lemma_i_m_list_exists(doc: Document, scope: Option<NodeId>, m: Seq<IComplex>, x: NodeId)
    ensures
        i_m_list(doc, scope, m, x) == exists|j: int|
            0 <= j < m.len() && i_m_complex(doc, scope, #[trigger] m[j], None, x),
{
    reveal_with_fuel(i_m_list, 2);
    if i_m_list(doc, scope, m, x) {
        let k = choose|k: int| 0 <= k < m.len() && i_m_complex(doc, scope, #[trigger] m[k], None, x);
        assert(0 <= k < m.len() && i_m_complex(doc, scope, m[k], None, x));
    }
    if exists|j: int| 0 <= j < m.len() && i_m_complex(doc, scope, #[trigger] m[j], None, x) {
        let k = choose|k: int| 0 <= k < m.len() && i_m_complex(doc, scope, #[trigger] m[k], None, x);
        assert(i_m_list(doc, scope, m, x));
    }
}

/// The first `k` selectors of a related list.
pub proof fn lemma_match_list_prefix(doc: Document, scope: Option<NodeId>, l: Seq<Complex>, m: Seq<IComplex>, k: int, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_list(l, m),
        0 <= k <= l.len(),
    ensures
        match_list(doc, l, k, x) == exists|j: int|
            0 <= j < k && i_m_complex(doc, scope, #[trigger] m[j], None, x),
    decreases l, 3nat, k,
{
    if k > 0 {
        lemma_match_list_prefix(doc, scope, l, m, k - 1, x);
        assert(rel_complex(l[k - 1], m[k - 1]));
        assert(m[k - 1].units.len() == l[k - 1].compounds.len());
        lemma_match_complex(doc, scope, l[k - 1], m[k - 1], l[k - 1].compounds.len() as int, x);
        assert(i_m_complex(doc, scope, m[k - 1], None, x) == i_m_at(
            doc,
            scope,
            m[k - 1],
            None,
            l[k - 1].compounds.len() - 1,
            x,
        ));
        if exists|j: int| 0 <= j < k && i_m_complex(doc, scope, #[trigger] m[j], None, x) {
            let j = choose|j: int| 0 <= j < k && i_m_complex(doc, scope, #[trigger] m[j], None, x);
            if j < k - 1 {
                assert(0 <= j < k - 1);
            }
        }
    }
}

/// **Matching.** A spec selector list matches an element exactly when its transcription does.
pub proof fn theorem_match_equivalent(doc: Document, scope: Option<NodeId>, l: Seq<Complex>, m: Seq<IComplex>, x: NodeId)
    requires
        wf(doc),
        uniq_attrs(doc),
        rel_list(l, m),
    ensures
        match_a_selector_against_an_element(doc, l, x) == i_match_selector(doc, scope, m, x),
{
    lemma_match_list(doc, scope, l, m, x);
    // A selector's compound selectors are not empty, so an element is needed to match.
    if !is_element(doc, x) {
        assert forall|j: int| 0 <= j < m.len() implies !i_m_complex(doc, scope, #[trigger] m[j], None, x) by {
            assert(rel_complex(l[j], m[j]));
            assert(!i_m_compound(doc, scope, m[j].units[m[j].units.len() - 1], x));
        }
    }
}

} // verus!
