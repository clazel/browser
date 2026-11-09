//! Theorems proven about the spec: the statements of [`super::contract`].

#[allow(unused_imports)]
use super::algorithm::*;
#[allow(unused_imports)]
use super::contract::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// theorem_match_total: the chain
// ------------------------------------------------------------------------------------

/// With enough fuel, the chain of `x` is its witness path.
proof fn lemma_chain_is_path(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId, fuel: nat)
    requires
        clazel_dom::spec::wf_with(doc, paths),
        x < doc.nodes.len(),
        fuel + 1 >= paths[x as int].len(),
    ensures
        chain_from(doc, x, fuel) == paths[x as int],
    decreases fuel,
{
    clazel_dom::lemmas::lemma_wf_split(doc, paths);
    clazel_dom::lemmas::lemma_path(doc, paths, x);
    match doc.nodes[x as int].parent {
        None => {
            assert(paths[x as int] == seq![x]);
        },
        Some(p) => {
            clazel_dom::lemmas::lemma_path(doc, paths, p);
            assert(paths[x as int] == paths[p as int].push(x));
            lemma_chain_is_path(doc, paths, p, (fuel - 1) as nat);
        },
    }
}

/// The chain of `x` in a well-formed arena: its nodes are nodes of the arena, the first has
/// no parent, each other's parent is the one before, and it ends in `x`.
proof fn lemma_chain(doc: Document, x: NodeId) -> (paths: Seq<Seq<NodeId>>)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
    ensures
        clazel_dom::spec::wf_with(doc, paths),
        chain(doc, x) == paths[x as int],
        chain(doc, x).len() >= 1,
        chain(doc, x).len() <= doc.nodes.len(),
        chain(doc, x)[chain(doc, x).len() - 1] == x,
        parent_of(doc, chain(doc, x)[0]) is None,
        forall|k: int| 0 <= k < chain(doc, x).len() ==> #[trigger] chain(doc, x)[k] < doc.nodes.len(),
        forall|k: int|
            0 < k < chain(doc, x).len() ==> parent_of(doc, #[trigger] chain(doc, x)[k]) == Some(
                chain(doc, x)[k - 1],
            ),
        forall|k: int|
            0 <= k < chain(doc, x).len() ==> paths[#[trigger] chain(doc, x)[k] as int].len() == k
                + 1,
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(doc);
    clazel_dom::lemmas::lemma_wf_split(doc, paths);
    clazel_dom::lemmas::lemma_path_facts(doc, paths, x);
    lemma_chain_is_path(doc, paths, x, doc.nodes.len());
    clazel_dom::lemmas::lemma_path(doc, paths, x);
    let ch = paths[x as int];
    assert forall|k: int| 0 <= k < ch.len() implies paths[#[trigger] ch[k] as int].len() == k + 1 by {
        assert(paths[ch[k] as int] == ch.subrange(0, k + 1));
    }
    // The root's path is itself alone, so it has no parent.
    let r = ch[0];
    assert(paths[r as int] == ch.subrange(0, 1));
    match doc.nodes[r as int].parent {
        None => {},
        Some(p) => {
            clazel_dom::lemmas::lemma_path(doc, paths, p);
            assert(paths[r as int] == paths[p as int].push(r));
            assert(false);
        },
    }
    assert forall|k: int| 0 < k < ch.len() implies parent_of(doc, #[trigger] ch[k]) == Some(ch[k - 1]) by {
        let y = ch[k];
        assert(paths[y as int] == ch.subrange(0, k + 1));
        match doc.nodes[y as int].parent {
            None => {
                assert(paths[y as int] == seq![y]);
            },
            Some(p) => {
                clazel_dom::lemmas::lemma_path(doc, paths, p);
                assert(paths[y as int] == paths[p as int].push(y));
                assert(paths[p as int] =~= ch.subrange(0, k));
                assert(p == paths[p as int].last());
            },
        }
    }
    paths
}

/// Enough fuel to reach the root is all [`some_ancestor_matches`] needs.
proof fn lemma_ancestors_fuel(
    doc: Document,
    paths: Seq<Seq<NodeId>>,
    c: Complex,
    n: int,
    y: NodeId,
    f1: nat,
    f2: nat,
)
    requires
        clazel_dom::spec::wf_with(doc, paths),
        y < doc.nodes.len(),
        f1 >= paths[y as int].len(),
        f2 >= paths[y as int].len(),
    ensures
        some_ancestor_matches(doc, c, n, Some(y), f1) == some_ancestor_matches(doc, c, n, Some(y), f2),
    decreases paths[y as int].len(),
{
    clazel_dom::lemmas::lemma_wf_split(doc, paths);
    clazel_dom::lemmas::lemma_path(doc, paths, y);
    assert(parent_of(doc, y) == doc.nodes[y as int].parent);
    assert(f1 > 0 && f2 > 0);
    match doc.nodes[y as int].parent {
        None => {
            assert(!some_ancestor_matches(doc, c, n, None, (f1 - 1) as nat));
            assert(!some_ancestor_matches(doc, c, n, None, (f2 - 1) as nat));
        },
        Some(p) => {
            clazel_dom::lemmas::lemma_path(doc, paths, p);
            assert(paths[y as int] == paths[p as int].push(y));
            lemma_ancestors_fuel(doc, paths, c, n, p, (f1 - 1) as nat, (f2 - 1) as nat);
        },
    }
    assert(some_ancestor_matches(doc, c, n, Some(y), f1) == ((is_element(doc, y) && match_complex(
        doc,
        c,
        n,
        y,
    )) || some_ancestor_matches(doc, c, n, parent_of(doc, y), (f1 - 1) as nat)));
    assert(some_ancestor_matches(doc, c, n, Some(y), f2) == ((is_element(doc, y) && match_complex(
        doc,
        c,
        n,
        y,
    )) || some_ancestor_matches(doc, c, n, parent_of(doc, y), (f2 - 1) as nat)));
}

// ------------------------------------------------------------------------------------
// theorem_match_total: one row
// ------------------------------------------------------------------------------------

/// A compound selector that is not empty matches no node that is not an element.
proof fn lemma_compound_needs_element(doc: Document, compound: Seq<Simple>, x: NodeId)
    requires
        compound.len() > 0,
        !is_element(doc, x),
    ensures
        !compound_matches(doc, compound, compound.len() as int, x),
{
    let k = compound.len() as int;
    assert(!simple_matches(doc, compound[k - 1], x));
    assert(compound_matches(doc, compound, k, x) == (compound_matches(doc, compound, k - 1, x)
        && simple_matches(doc, compound[k - 1], x)));
}

/// The relation the spec checks for the first `i + 1` compound selectors at `s`, `i >= 1`:
/// the branch of [`match_complex`] for its rightmost combinator.
pub open spec fn relation_holds(doc: Document, c: Complex, i: int, s: NodeId) -> bool {
    match c.combinators[i - 1] {
        Combinator::Descendant => some_ancestor_matches(doc, c, i, parent_of(doc, s), doc.nodes.len()),
        Combinator::Child => match parent_of(doc, s) {
            Some(p) => is_element(doc, p) && match_complex(doc, c, i, p),
            None => false,
        },
        Combinator::NextSibling => previous_element_matches(
            doc,
            c,
            i,
            inclusive_siblings(doc, s),
            sibling_index(doc, s) - 1,
        ),
        Combinator::SubsequentSibling => some_earlier_sibling_matches(
            doc,
            c,
            i,
            inclusive_siblings(doc, s),
            sibling_index(doc, s) - 1,
        ),
    }
}

/// A row is right when the relations it reads are.
proof fn lemma_row(
    doc: Document,
    c: Complex,
    s: NodeId,
    parent: Seq<bool>,
    descendant: Seq<bool>,
    previous: Seq<bool>,
    earlier: Seq<bool>,
)
    requires
        complex_wf(c),
        forall|i: int|
            1 <= i < c.compounds.len() ==> #[trigger] related(
                c.combinators[i - 1],
                i - 1,
                parent,
                descendant,
                previous,
                earlier,
            ) == relation_holds(doc, c, i, s),
    ensures
        forall|i: int|
            0 <= i < c.compounds.len() ==> #[trigger] row(doc, c, s, parent, descendant, previous, earlier)[i]
                == match_complex(doc, c, i + 1, s),
{
    let n = c.compounds.len();
    assert forall|i: int| 0 <= i < n implies #[trigger] row(doc, c, s, parent, descendant, previous, earlier)[i]
        == match_complex(doc, c, i + 1, s) by {
        super::exec_match::lemma_compounds_wf_at(c, n as int, i);
        if !is_element(doc, s) {
            lemma_compound_needs_element(doc, c.compounds[i], s);
        }
        if i >= 1 {
            assert(related(c.combinators[i - 1], i - 1, parent, descendant, previous, earlier)
                == relation_holds(doc, c, i, s));
        }
    }
}

/// Without `+` or `~`, no combinator is one.
proof fn lemma_no_siblings(c: Complex, k: int, i: int)
    requires
        !sibling_combinator_within(c, k),
        0 <= i < k <= c.combinators.len(),
    ensures
        c.combinators[i] != Combinator::NextSibling,
        c.combinators[i] != Combinator::SubsequentSibling,
    decreases k,
{
    if i < k - 1 {
        lemma_no_siblings(c, k - 1, i);
    }
}

// ------------------------------------------------------------------------------------
// theorem_match_total: siblings and levels
// ------------------------------------------------------------------------------------

/// The walk along the children of `p` gives the spec's sibling relations, as long as `p`'s
/// row and the descendant row are right.
proof fn lemma_siblings(
    doc: Document,
    paths: Seq<Seq<NodeId>>,
    c: Complex,
    p: NodeId,
    parent: Seq<bool>,
    descendant: Seq<bool>,
    j: int,
)
    requires
        clazel_dom::spec::wf_with(doc, paths),
        complex_wf(c),
        p < doc.nodes.len(),
        0 <= j <= children_of(doc, p).len(),
        parent.len() == c.compounds.len(),
        descendant.len() == c.compounds.len(),
        forall|i: int| 0 <= i < c.compounds.len() ==> #[trigger] parent[i] == match_complex(doc, c, i + 1, p),
        forall|i: int|
            0 <= i < c.compounds.len() ==> #[trigger] descendant[i] == some_ancestor_matches(
                doc,
                c,
                i + 1,
                Some(p),
                doc.nodes.len(),
            ),
    ensures
        ({
            let w = siblings_loop(doc, c, children_of(doc, p), j, parent, descendant);
            &&& w.previous.len() == c.compounds.len()
            &&& w.earlier.len() == c.compounds.len()
            &&& forall|i: int|
                0 <= i < c.compounds.len() ==> #[trigger] w.previous[i] == previous_element_matches(
                    doc,
                    c,
                    i + 1,
                    children_of(doc, p),
                    j - 1,
                )
            &&& forall|i: int|
                0 <= i < c.compounds.len() ==> #[trigger] w.earlier[i]
                    == some_earlier_sibling_matches(doc, c, i + 1, children_of(doc, p), j - 1)
            &&& w.work <= c.compounds.len() * j
        }),
    decreases j,
{
    let n = c.compounds.len();
    let kids = children_of(doc, p);
    if j > 0 {
        lemma_siblings(doc, paths, c, p, parent, descendant, j - 1);
        let before = siblings_loop(doc, c, kids, j - 1, parent, descendant);
        let s = kids[j - 1];
        clazel_dom::lemmas::lemma_wf_split(doc, paths);
        assert(doc.nodes[p as int].children[j - 1] == s);
        assert(s < doc.nodes.len() && doc.nodes[s as int].parent == Some(p));
        assert(doc.nodes[p as int].children.no_duplicates());
        clazel_dom::lemmas::lemma_index_of_unique(kids, j - 1);
        if is_element(doc, s) {
            assert forall|i: int|
                1 <= i < n implies #[trigger] related(
                c.combinators[i - 1],
                i - 1,
                parent,
                descendant,
                before.previous,
                before.earlier,
            ) == relation_holds(doc, c, i, s) by {
                if p < doc.nodes.len() {
                    assert(parent[i - 1] == match_complex(doc, c, i, p));
                    if !is_element(doc, p) {
                        super::exec_match::lemma_compounds_wf_at(c, n as int, i - 1);
                        lemma_compound_needs_element(doc, c.compounds[i - 1], p);
                    }
                }
            }
            lemma_row(doc, c, s, parent, descendant, before.previous, before.earlier);
            let r = row(doc, c, s, parent, descendant, before.previous, before.earlier);
            let w = siblings_loop(doc, c, kids, j, parent, descendant);
            assert forall|i: int| 0 <= i < n implies #[trigger] w.earlier[i]
                == some_earlier_sibling_matches(doc, c, i + 1, kids, j - 1) by {
                assert(w.earlier[i] == (before.earlier[i] || r[i]));
            }
            assert(w.work == before.work + n);
            assert(n * (j - 1) + n == n * j) by (nonlinear_arith);
        } else {
            assert(n * (j - 1) <= n * j) by (nonlinear_arith)
                requires j >= 1;
        }
    }
}

/// What a level of the walk holds at chain node `k`.
pub open spec fn level_right(doc: Document, c: Complex, ch: Seq<NodeId>, k: int, siblings: bool) -> bool {
    let lv = level(doc, c, ch, k, siblings);
    &&& lv.row.len() == c.compounds.len()
    &&& lv.descendant.len() == c.compounds.len()
    &&& forall|i: int| 0 <= i < c.compounds.len() ==> #[trigger] lv.row[i] == match_complex(doc, c, i + 1, ch[k])
    &&& forall|i: int|
        0 <= i < c.compounds.len() ==> #[trigger] lv.descendant[i] == some_ancestor_matches(
            doc,
            c,
            i + 1,
            parent_of(doc, ch[k]),
            doc.nodes.len(),
        )
    &&& lv.work <= c.compounds.len() * if siblings {
        context_from(doc, ch, k)
    } else {
        (k + 1) as nat
    }
}

/// The root of the chain.
#[verifier::spinoff_prover]
proof fn lemma_level_root(doc: Document, c: Complex, x: NodeId, siblings: bool)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
    ensures
        level_right(doc, c, chain(doc, x), 0, siblings),
{
    let ch = chain(doc, x);
    let n = c.compounds.len();
    let paths = lemma_chain(doc, x);
    let none = falses(n);
    let r0 = ch[0];
    // The root of the chain has no parent, so no ancestors and no other siblings.
    assert(inclusive_siblings(doc, r0) == seq![r0]);
    assert(clazel_dom::spec::index_of(seq![r0], r0) == 0);
    assert forall|i: int|
        1 <= i < n implies #[trigger] related(c.combinators[i - 1], i - 1, none, none, none, none)
        == relation_holds(doc, c, i, r0) by {}
    lemma_row(doc, c, r0, none, none, none, none);
    assert(n * 1 == n);
}

/// The descendant row below chain node `k - 1`: that node, or one of its ancestors.
#[verifier::spinoff_prover]
proof fn lemma_level_descendant(doc: Document, c: Complex, x: NodeId, k: int, siblings: bool)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
        0 < k < chain(doc, x).len(),
        level_right(doc, c, chain(doc, x), k - 1, siblings),
    ensures
        ({
            let ch = chain(doc, x);
            let up = level(doc, c, ch, k - 1, siblings);
            let descendant = or_rows(up.row, up.descendant);
            &&& descendant.len() == c.compounds.len()
            &&& forall|i: int|
                0 <= i < c.compounds.len() ==> #[trigger] descendant[i] == some_ancestor_matches(
                    doc,
                    c,
                    i + 1,
                    Some(ch[k - 1]),
                    doc.nodes.len(),
                )
        }),
{
    let ch = chain(doc, x);
    let n = c.compounds.len();
    let paths = lemma_chain(doc, x);
    let up = level(doc, c, ch, k - 1, siblings);
    let descendant = or_rows(up.row, up.descendant);
    let p = ch[k - 1];
    assert(p < doc.nodes.len());
    assert forall|i: int| 0 <= i < n implies #[trigger] descendant[i] == some_ancestor_matches(
        doc,
        c,
        i + 1,
        Some(p),
        doc.nodes.len(),
    ) by {
        super::exec_match::lemma_compounds_wf_at(c, n as int, i);
        if !is_element(doc, p) {
            lemma_compound_needs_element(doc, c.compounds[i], p);
        }
        assert(up.row[i] == match_complex(doc, c, i + 1, p));
        match parent_of(doc, p) {
            None => {},
            Some(q) => {
                assert(k - 1 > 0);
                assert(q == ch[k - 2]);
                lemma_ancestors_fuel(
                    doc,
                    paths,
                    c,
                    i + 1,
                    q,
                    (doc.nodes.len() - 1) as nat,
                    doc.nodes.len(),
                );
            },
        }
    }
}

/// Chain node `k` is a child of node `k - 1`, at its index among their children.
#[verifier::spinoff_prover]
proof fn lemma_chain_child(doc: Document, x: NodeId, k: int)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        0 < k < chain(doc, x).len(),
    ensures
        ({
            let ch = chain(doc, x);
            let kids = children_of(doc, ch[k - 1]);
            let target = clazel_dom::spec::index_of(kids, ch[k]);
            &&& ch[k - 1] < doc.nodes.len()
            &&& ch[k] < doc.nodes.len()
            &&& parent_of(doc, ch[k]) == Some(ch[k - 1])
            &&& 0 <= target < kids.len()
            &&& inclusive_siblings(doc, ch[k]) == kids
        }),
{
    let ch = chain(doc, x);
    let paths = lemma_chain(doc, x);
    clazel_dom::lemmas::lemma_wf_split(doc, paths);
    let p = ch[k - 1];
    let y = ch[k];
    let kids = children_of(doc, p);
    assert(doc.nodes[y as int].parent == Some(p));
    assert(doc.nodes[p as int].children.contains(y));
    clazel_dom::lemmas::lemma_index_of(kids, y);
}

/// The relations a row at `y` reads are right when its inputs are.
#[verifier::spinoff_prover]
proof fn lemma_relations(
    doc: Document,
    c: Complex,
    p: NodeId,
    y: NodeId,
    kids: Seq<NodeId>,
    target: int,
    parent: Seq<bool>,
    descendant: Seq<bool>,
    previous: Seq<bool>,
    earlier: Seq<bool>,
)
    requires
        complex_wf(c),
        parent_of(doc, y) == Some(p),
        inclusive_siblings(doc, y) == kids,
        clazel_dom::spec::index_of(kids, y) == target,
        parent.len() == c.compounds.len(),
        forall|i: int| 0 <= i < c.compounds.len() ==> #[trigger] parent[i] == match_complex(doc, c, i + 1, p),
        forall|i: int|
            0 <= i < c.compounds.len() ==> #[trigger] descendant[i] == some_ancestor_matches(
                doc,
                c,
                i + 1,
                Some(p),
                doc.nodes.len(),
            ),
        forall|i: int|
            0 <= i < c.compounds.len() ==> #[trigger] previous[i] == previous_element_matches(
                doc,
                c,
                i + 1,
                kids,
                target - 1,
            ),
        forall|i: int|
            0 <= i < c.compounds.len() ==> #[trigger] earlier[i] == some_earlier_sibling_matches(
                doc,
                c,
                i + 1,
                kids,
                target - 1,
            ),
    ensures
        forall|i: int|
            1 <= i < c.compounds.len() ==> #[trigger] related(
                c.combinators[i - 1],
                i - 1,
                parent,
                descendant,
                previous,
                earlier,
            ) == relation_holds(doc, c, i, y),
{
    let n = c.compounds.len();
    assert(sibling_index(doc, y) == target);
    assert forall|i: int|
        1 <= i < n implies #[trigger] related(
        c.combinators[i - 1],
        i - 1,
        parent,
        descendant,
        previous,
        earlier,
    ) == relation_holds(doc, c, i, y) by {
        super::exec_match::lemma_compounds_wf_at(c, n as int, i - 1);
        if !is_element(doc, p) {
            lemma_compound_needs_element(doc, c.compounds[i - 1], p);
        }
        assert(parent[i - 1] == match_complex(doc, c, i, p));
        assert(descendant[i - 1] == some_ancestor_matches(doc, c, i, Some(p), doc.nodes.len()));
        assert(previous[i - 1] == previous_element_matches(doc, c, i, kids, target - 1));
        assert(earlier[i - 1] == some_earlier_sibling_matches(doc, c, i, kids, target - 1));
    }
}

/// The relations at chain node `k` with siblings, and the work.
#[verifier::spinoff_prover]
proof fn lemma_level_step_siblings(doc: Document, c: Complex, x: NodeId, k: int)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
        uses_siblings(c),
        0 < k < chain(doc, x).len(),
        level_right(doc, c, chain(doc, x), k - 1, true),
    ensures
        level_right(doc, c, chain(doc, x), k, true),
{
    let ch = chain(doc, x);
    let n = c.compounds.len();
    let paths = lemma_chain(doc, x);
    lemma_level_descendant(doc, c, x, k, true);
    lemma_chain_child(doc, x, k);
    let up = level(doc, c, ch, k - 1, true);
    let p = ch[k - 1];
    let y = ch[k];
    let descendant = or_rows(up.row, up.descendant);
    let kids = children_of(doc, p);
    let target = clazel_dom::spec::index_of(kids, y);
    lemma_siblings(doc, paths, c, p, up.row, descendant, target);
    let w = siblings_loop(doc, c, kids, target, up.row, descendant);
    lemma_relations(doc, c, p, y, kids, target, up.row, descendant, w.previous, w.earlier);
    lemma_row(doc, c, y, up.row, descendant, w.previous, w.earlier);
    let lv = level(doc, c, ch, k, true);
    assert(lv.row == row(doc, c, y, up.row, descendant, w.previous, w.earlier));
    assert(lv.descendant == descendant);
    assert(lv.work == up.work + w.work + n);
    let ctx = context_from(doc, ch, k - 1);
    assert(context_from(doc, ch, k) == ctx + (target + 1) as nat);
    assert(up.work <= n * ctx);
    assert(w.work <= n * target);
    assert(n * ctx + n * target + n == n * (ctx + target + 1)) by (nonlinear_arith);
}

/// The relations at chain node `k` without siblings, and the work.
#[verifier::spinoff_prover]
proof fn lemma_level_step_plain(doc: Document, c: Complex, x: NodeId, k: int)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
        !uses_siblings(c),
        0 < k < chain(doc, x).len(),
        level_right(doc, c, chain(doc, x), k - 1, false),
    ensures
        level_right(doc, c, chain(doc, x), k, false),
{
    let ch = chain(doc, x);
    let n = c.compounds.len();
    lemma_level_descendant(doc, c, x, k, false);
    lemma_chain_child(doc, x, k);
    let up = level(doc, c, ch, k - 1, false);
    let p = ch[k - 1];
    let y = ch[k];
    let descendant = or_rows(up.row, up.descendant);
    let none = falses(n);
    assert forall|i: int|
        1 <= i < n implies #[trigger] related(c.combinators[i - 1], i - 1, up.row, descendant, none, none)
        == relation_holds(doc, c, i, y) by {
        lemma_no_siblings(c, c.combinators.len() as int, i - 1);
        super::exec_match::lemma_compounds_wf_at(c, n as int, i - 1);
        if !is_element(doc, p) {
            lemma_compound_needs_element(doc, c.compounds[i - 1], p);
        }
    }
    lemma_row(doc, c, y, up.row, descendant, none, none);
    assert(n * k + n == n * (k + 1)) by (nonlinear_arith);
}

/// Chain node `k` from node `k - 1`.
proof fn lemma_level_step(doc: Document, c: Complex, x: NodeId, k: int, siblings: bool)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
        siblings == uses_siblings(c),
        0 < k < chain(doc, x).len(),
        level_right(doc, c, chain(doc, x), k - 1, siblings),
    ensures
        level_right(doc, c, chain(doc, x), k, siblings),
{
    if siblings {
        lemma_level_step_siblings(doc, c, x, k);
    } else {
        lemma_level_step_plain(doc, c, x, k);
    }
}

/// Each level of the walk holds the spec's rows.
proof fn lemma_levels(doc: Document, c: Complex, x: NodeId, k: int, siblings: bool)
    requires
        clazel_dom::spec::wf(doc),
        x < doc.nodes.len(),
        complex_wf(c),
        siblings == uses_siblings(c),
        0 <= k < chain(doc, x).len(),
    ensures
        level_right(doc, c, chain(doc, x), k, siblings),
    decreases k,
{
    if k == 0 {
        lemma_level_root(doc, c, x, siblings);
    } else {
        lemma_levels(doc, c, x, k - 1, siblings);
        lemma_level_step(doc, c, x, k, siblings);
    }
}

/// `theorem_match_total` ([`match_total`]).
pub proof fn theorem_match_total(doc: Document, c: Complex, x: NodeId)
    ensures
        match_total(doc, c, x),
{
    if match_requires(doc, x) && complex_wf(c) {
        let paths = lemma_chain(doc, x);
        let ch = chain(doc, x);
        let siblings = uses_siblings(c);
        lemma_levels(doc, c, x, ch.len() - 1, siblings);
        assert(ch[ch.len() - 1] == x);
    }
}

} // verus!
