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
use super::independent_equivalence::*;
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

} // verus!
