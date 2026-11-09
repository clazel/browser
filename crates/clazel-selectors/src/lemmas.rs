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

verus! {

// ------------------------------------------------------------------------------------
// theorem_parse_total
// ------------------------------------------------------------------------------------

/// [`compound_wf`] reads only the first `k` simple selectors.
proof fn lemma_compound_wf_prefix(a: Seq<Simple>, b: Seq<Simple>, k: int)
    requires
        0 <= k <= a.len(),
        k <= b.len(),
        forall|j: int| 0 <= j < k ==> a[j] == b[j],
    ensures
        compound_wf(a, k) == compound_wf(b, k),
    decreases k,
{
    if k > 0 {
        lemma_compound_wf_prefix(a, b, k - 1);
    }
}

/// A well-formed compound selector with one more well-formed simple selector.
proof fn lemma_compound_wf_push(acc: Seq<Simple>, s: Simple)
    requires
        compound_wf(acc, acc.len() as int),
        simple_wf(s),
    ensures
        compound_wf(acc.push(s), acc.len() as int + 1),
{
    lemma_compound_wf_prefix(acc, acc.push(s), acc.len() as int);
}

/// [`compounds_wf`] reads only the first `n` compound selectors.
proof fn lemma_compounds_wf_prefix(a: Complex, b: Complex, n: int)
    requires
        0 <= n <= a.compounds.len(),
        n <= b.compounds.len(),
        forall|j: int| 0 <= j < n ==> a.compounds[j] == b.compounds[j],
    ensures
        compounds_wf(a, n) == compounds_wf(b, n),
    decreases n,
{
    if n > 0 {
        lemma_compounds_wf_prefix(a, b, n - 1);
    }
}

/// [`list_wf`] reads only the first `k` complex selectors.
proof fn lemma_list_wf_prefix(a: Seq<Complex>, b: Seq<Complex>, k: int)
    requires
        0 <= k <= a.len(),
        k <= b.len(),
        forall|j: int| 0 <= j < k ==> a[j] == b[j],
    ensures
        list_wf(a, k) == list_wf(b, k),
    decreases k,
{
    if k > 0 {
        lemma_list_wf_prefix(a, b, k - 1);
    }
}

/// A well-formed list with one more well-formed complex selector.
proof fn lemma_list_wf_push(acc: Seq<Complex>, c: Complex)
    requires
        list_wf(acc, acc.len() as int),
        complex_wf(c),
    ensures
        list_wf(acc.push(c), acc.len() as int + 1),
{
    lemma_list_wf_prefix(acc, acc.push(c), acc.len() as int);
}

/// A simple selector of the grammar's leaves is well-formed.
proof fn lemma_leaf_wf(s: Simple)
    requires
        !(s is Is) && !(s is Where) && !(s is Not),
    ensures
        simple_wf(s),
{
}

/// What [`user_actions`] adds is well-formed, and it moves on only by adding.
proof fn lemma_user_actions(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>)
    requires
        compound_wf(acc, acc.len() as int),
    ensures
        match user_actions(items, i, hi, acc) {
            Some((out, next)) => compound_wf(out, out.len() as int) && out.len() >= acc.len()
                && next >= i,
            None => true,
        },
    decreases hi - i,
{
    match user_action(items, i, hi) {
        Step::Found { value, next } => if next > i && next <= hi {
            lemma_compound_wf_push(acc, Simple::PseudoClass { class: value });
            lemma_user_actions(items, next, hi, acc.push(Simple::PseudoClass { class: value }));
        },
        _ => {},
    }
}

/// What [`pseudo_compound`] adds is well-formed, and it moves on only by adding.
proof fn lemma_pseudo_compound(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, no_pseudo: bool)
    requires
        compound_wf(acc, acc.len() as int),
    ensures
        match pseudo_compound(items, i, hi, acc, no_pseudo) {
            Some((out, next)) => compound_wf(out, out.len() as int) && out.len() >= acc.len() && next
                >= i && (next > i ==> out.len() > acc.len()),
            None => true,
        },
{
    match pseudo_element(items, i, hi) {
        Step::Found { value, next } => if !no_pseudo {
            let pushed = acc.push(Simple::PseudoElement { element: value });
            lemma_compound_wf_push(acc, Simple::PseudoElement { element: value });
            lemma_user_actions(items, next, hi, pushed);
        },
        _ => {},
    }
}

/// [`functional_pseudo_class`] gives a well-formed simple selector.
proof fn lemma_functional(name: Seq<u32>, value: Seq<ComponentValue>)
    ensures
        match functional_pseudo_class(name, value) {
            Some(s) => simple_wf(s),
            None => true,
        },
    decreases value, value.len() + 1, 0int,
{
    if ascii_case_insensitive_match(name, str_is()) || ascii_case_insensitive_match(name, str_where()) {
        lemma_forgiving(value);
    } else if ascii_case_insensitive_match(name, str_not()) {
        lemma_complex_list_loop(value, 0, value.len() as int, Seq::empty(), true);
    }
}

/// [`subclass_selector`] gives a well-formed simple selector, after `i`.
proof fn lemma_subclass(items: Seq<ComponentValue>, i: int, hi: int)
    ensures
        match subclass_selector(items, i, hi) {
            Step::Found { value, next } => simple_wf(value) && next > i,
            _ => true,
        },
    decreases items, hi - i, 0int,
{
    if !(i < 0 || i >= hi || hi > items.len()) {
        match items[i] {
            ComponentValue::Token { token: Token::Colon } => {
                if !is_token_at(items, i + 1, hi, Token::Colon) && i + 1 < hi {
                    match items[i + 1] {
                        ComponentValue::Function { name, value } => {
                            lemma_functional(name, value);
                        },
                        _ => {},
                    }
                }
            },
            _ => {},
        }
    }
}

/// [`subclass_selectors`] keeps the simple selectors well-formed, and moves on only by
/// adding.
proof fn lemma_subclasses(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>, no_pseudo: bool)
    requires
        compound_wf(acc, acc.len() as int),
    ensures
        match subclass_selectors(items, i, hi, acc, no_pseudo) {
            Some((out, next)) => compound_wf(out, out.len() as int) && out.len() >= acc.len() && next
                >= i && (next > i ==> out.len() > acc.len()),
            None => true,
        },
    decreases items, hi - i, 1int,
{
    lemma_subclass(items, i, hi);
    match subclass_selector(items, i, hi) {
        Step::Found { value, next } => if i < next && next <= hi {
            lemma_compound_wf_push(acc, value);
            lemma_subclasses(items, next, hi, acc.push(value), no_pseudo);
        },
        Step::Absent => {
            lemma_pseudo_compound(items, i, hi, acc, no_pseudo);
        },
        Step::Invalid => {},
    }
}

/// A compound selector that read something is not empty, and is well-formed.
proof fn lemma_compound(items: Seq<ComponentValue>, i: int, hi: int, no_pseudo: bool)
    ensures
        match compound_selector(items, i, hi, no_pseudo) {
            Some((out, next)) => compound_wf(out, out.len() as int) && (next > i ==> out.len() > 0),
            None => true,
        },
    decreases items, hi - i, 2int,
{
    match type_selector(items, i, hi) {
        Step::Invalid => {},
        Step::Absent => {
            lemma_subclasses(items, i, hi, Seq::empty(), no_pseudo);
        },
        Step::Found { value, next } => if i < next && next <= hi {
            lemma_leaf_wf(value);
            lemma_compound_wf_push(Seq::empty(), value);
            assert(Seq::<Simple>::empty().push(value) == seq![value]);
            lemma_subclasses(items, next, hi, seq![value], no_pseudo);
        },
    }
}

/// The loop of [`complex_selector_loop`] keeps one combinator fewer than compounds, all
/// well-formed.
proof fn lemma_complex_loop(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    compounds: Seq<Seq<Simple>>,
    combinators: Seq<Combinator>,
    no_pseudo: bool,
)
    requires
        compounds.len() == combinators.len(),
        compounds_wf(Complex { compounds, combinators }, compounds.len() as int),
    ensures
        match complex_selector_loop(items, i, hi, compounds, combinators, no_pseudo) {
            Some(c) => complex_wf(c),
            None => true,
        },
    decreases items, hi - i, 3int,
{
    lemma_compound(items, i, hi, no_pseudo);
    match compound_selector(items, i, hi, no_pseudo) {
        None => {},
        Some((compound, next)) => if !(next <= i || next > hi) {
            let more = compounds.push(compound);
            let after = skip_whitespace(items, next, hi);
            lemma_compounds_wf_prefix(
                Complex { compounds, combinators },
                Complex { compounds: more, combinators },
                compounds.len() as int,
            );
            let c1 = Complex { compounds: more, combinators };
            assert(compounds_wf(c1, more.len() as int));
            if after < hi && !has_pseudo_element(compound) {
                match combinator_at(items, after, hi) {
                    Some(combinator) => {
                        let start = skip_whitespace(items, after + 1, hi);
                        if start < hi {
                            let c2 = Complex { compounds: more, combinators: combinators.push(combinator) };
                            lemma_compounds_wf_prefix(c1, c2, more.len() as int);
                            lemma_complex_loop(items, start, hi, more, combinators.push(combinator), no_pseudo);
                        }
                    },
                    None => if after > next {
                        let c2 = Complex {
                            compounds: more,
                            combinators: combinators.push(Combinator::Descendant),
                        };
                        lemma_compounds_wf_prefix(c1, c2, more.len() as int);
                        lemma_complex_loop(
                            items,
                            after,
                            hi,
                            more,
                            combinators.push(Combinator::Descendant),
                            no_pseudo,
                        );
                    },
                }
            }
        },
    }
}

/// [`complex_selector`] gives a well-formed complex selector.
proof fn lemma_complex(items: Seq<ComponentValue>, lo: int, hi: int, no_pseudo: bool)
    ensures
        match complex_selector(items, lo, hi, no_pseudo) {
            Some(c) => complex_wf(c),
            None => true,
        },
    decreases items, hi - lo, 4int,
{
    let start = skip_whitespace(items, lo, hi);
    if !(start >= hi || start < lo) {
        lemma_complex_loop(items, start, hi, Seq::empty(), Seq::empty(), no_pseudo);
    }
}

/// [`complex_list_loop`] gives one or more well-formed complex selectors.
proof fn lemma_complex_list_loop(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>, no_pseudo: bool)
    requires
        list_wf(acc, acc.len() as int),
    ensures
        match complex_list_loop(items, i, hi, acc, no_pseudo) {
            Some(list) => list.len() > 0 && list_wf(list, list.len() as int),
            None => true,
        },
    decreases items, hi - i, 5int,
{
    let comma = next_comma(items, i, hi);
    if !(i < 0 || comma < i || comma > hi) {
        lemma_complex(items, i, comma, no_pseudo);
        match complex_selector(items, i, comma, no_pseudo) {
            None => {},
            Some(selector) => {
                lemma_list_wf_push(acc, selector);
                if comma < hi {
                    lemma_complex_list_loop(items, comma + 1, hi, acc.push(selector), no_pseudo);
                }
            },
        }
    }
}

/// [`forgiving_list_loop`] keeps only well-formed complex selectors.
proof fn lemma_forgiving_loop(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Complex>)
    requires
        list_wf(acc, acc.len() as int),
    ensures
        ({
            let list = forgiving_list_loop(items, i, hi, acc);
            list_wf(list, list.len() as int)
        }),
    decreases items, hi - i, 5int,
{
    let comma = next_comma(items, i, hi);
    if !(i < 0 || i >= hi || comma < i || comma > hi) {
        lemma_complex(items, i, comma, true);
        let kept = match complex_selector(items, i, comma, true) {
            Some(selector) => {
                lemma_list_wf_push(acc, selector);
                acc.push(selector)
            },
            None => acc,
        };
        if comma < hi {
            lemma_forgiving_loop(items, comma + 1, hi, kept);
        }
    }
}

/// "Parse as a forgiving selector list" gives a well-formed list.
proof fn lemma_forgiving(value: Seq<ComponentValue>)
    ensures
        ({
            let list = parse_as_a_forgiving_selector_list(value);
            list_wf(list, list.len() as int)
        }),
    decreases value, value.len() as int, 7int,
{
    if !only_whitespace(value, 0, value.len() as int) {
        lemma_forgiving_loop(value, 0, value.len() as int, Seq::empty());
    }
}

/// `theorem_parse_total` ([`parse_total`]).
pub proof fn theorem_parse_total(source: Seq<u32>)
    ensures
        parse_total(source),
{
    let values = parse_a_list_of_component_values(Input::String { string: source });
    lemma_complex_list_loop(values, 0, values.len() as int, Seq::empty(), false);
}

// ------------------------------------------------------------------------------------
// Specificity
// ------------------------------------------------------------------------------------

/// Every component of a sum is at most the limit.
proof fn lemma_add_bounded(x: Specificity, y: Specificity)
    ensures
        add_specificity(x, y).a <= specificity_limit(),
        add_specificity(x, y).b <= specificity_limit(),
        add_specificity(x, y).c <= specificity_limit(),
        add_specificity(x, y).a >= x.a || x.a > specificity_limit(),
        add_specificity(x, y).b >= x.b || x.b > specificity_limit(),
        add_specificity(x, y).c >= x.c || x.c > specificity_limit(),
{
}

/// A compound selector's specificity is within the limit.
proof fn lemma_compound_bounded(compound: Seq<Simple>, k: int)
    ensures
        compound_specificity(compound, k).a <= specificity_limit(),
        compound_specificity(compound, k).b <= specificity_limit(),
        compound_specificity(compound, k).c <= specificity_limit(),
{
    if 0 < k <= compound.len() {
        lemma_add_bounded(compound_specificity(compound, k - 1), simple_specificity(compound[k - 1]));
    }
}

/// A complex selector's specificity is within the limit.
proof fn lemma_complex_bounded(c: Complex, n: int)
    ensures
        complex_specificity(c, n).a <= specificity_limit(),
        complex_specificity(c, n).b <= specificity_limit(),
        complex_specificity(c, n).c <= specificity_limit(),
{
    if 0 < n <= c.compounds.len() {
        lemma_add_bounded(
            complex_specificity(c, n - 1),
            compound_specificity(c.compounds[n - 1], c.compounds[n - 1].len() as int),
        );
    }
}

/// Adding never lowers a specificity within the limit.
proof fn lemma_add_not_less(x: Specificity, y: Specificity)
    requires
        x.a <= specificity_limit(),
        x.b <= specificity_limit(),
        x.c <= specificity_limit(),
    ensures
        not_more_specific(x, add_specificity(x, y)),
{
}

/// [`compound_specificity`] reads only the first `k` simple selectors.
proof fn lemma_compound_specificity_prefix(a: Seq<Simple>, b: Seq<Simple>, k: int)
    requires
        0 <= k <= a.len(),
        k <= b.len(),
        forall|j: int| 0 <= j < k ==> a[j] == b[j],
    ensures
        compound_specificity(a, k) == compound_specificity(b, k),
    decreases k,
{
    if k > 0 {
        lemma_compound_specificity_prefix(a, b, k - 1);
    }
}

/// [`complex_specificity`] reads only the first `n` compound selectors.
proof fn lemma_complex_specificity_prefix(a: Complex, b: Complex, n: int)
    requires
        0 <= n <= a.compounds.len(),
        n <= b.compounds.len(),
        forall|j: int| 0 <= j < n ==> a.compounds[j] == b.compounds[j],
    ensures
        complex_specificity(a, n) == complex_specificity(b, n),
    decreases n,
{
    if n > 0 {
        lemma_complex_specificity_prefix(a, b, n - 1);
    }
}

/// `theorem_specificity_monotone` ([`specificity_monotone`]).
pub proof fn theorem_specificity_monotone(compound: Seq<Simple>, s: Simple, c: Complex, more: Seq<Simple>)
    ensures
        specificity_monotone(compound, s, c, more),
{
    let k = compound.len() as int;
    let pushed = compound.push(s);
    lemma_compound_specificity_prefix(compound, pushed, k);
    lemma_compound_bounded(compound, k);
    lemma_add_not_less(compound_specificity(compound, k), simple_specificity(s));
    let n = c.compounds.len() as int;
    let longer = Complex { compounds: c.compounds.push(more), combinators: c.combinators };
    lemma_complex_specificity_prefix(c, longer, n);
    lemma_complex_bounded(c, n);
    lemma_add_not_less(
        complex_specificity(c, n),
        compound_specificity(more, more.len() as int),
    );
}

/// `theorem_where_zero` ([`where_is_zero`]).
pub proof fn theorem_where_zero(arg: Seq<Complex>, compound: Seq<Simple>)
    ensures
        where_is_zero(arg, compound),
{
    let k = compound.len() as int;
    let pushed = compound.push(Simple::Where { arg });
    lemma_compound_specificity_prefix(compound, pushed, k);
    lemma_compound_bounded(compound, k);
    let x = compound_specificity(compound, k);
    assert(simple_specificity(Simple::Where { arg }) == zero());
    assert(pushed[k] == Simple::Where { arg });
    assert(compound_specificity(pushed, k + 1) == add_specificity(
        compound_specificity(pushed, k),
        simple_specificity(pushed[k]),
    ));
    assert(add_specificity(x, zero()) == x);
}

/// [`not_more_specific`] is transitive.
proof fn lemma_order_transitive(x: Specificity, y: Specificity, z: Specificity)
    requires
        not_more_specific(x, y),
        not_more_specific(y, z),
    ensures
        not_more_specific(x, z),
{
}

/// [`list_specificity`] of the first `k` is the most specific of them.
proof fn lemma_list_specificity(arg: Seq<Complex>, k: int)
    requires
        0 <= k <= arg.len(),
    ensures
        forall|i: int| 0 <= i < k ==> not_more_specific(#[trigger] specificity(arg[i]), list_specificity(arg, k)),
        k == 0 ==> list_specificity(arg, k) == zero(),
        k > 0 ==> exists|i: int| 0 <= i < k && list_specificity(arg, k) == #[trigger] specificity(arg[i]),
    decreases k,
{
    if k > 0 {
        lemma_list_specificity(arg, k - 1);
        let before = list_specificity(arg, k - 1);
        let last = specificity(arg[k - 1]);
        let now = list_specificity(arg, k);
        assert(now == most_specific(before, last));
        assert forall|i: int| 0 <= i < k implies not_more_specific(#[trigger] specificity(arg[i]), now) by {
            if i < k - 1 {
                if not_more_specific(before, last) {
                    lemma_order_transitive(specificity(arg[i]), before, last);
                }
            }
        }
        if k - 1 == 0 {
            assert(now == last || now == before);
            if now == before {
                // before is zero, which is at most as specific as anything.
                assert(not_more_specific(before, last));
            }
            assert(now == specificity(arg[0]));
        } else {
            if now == last {
                assert(now == specificity(arg[k - 1]));
            } else {
                let i = choose|i: int| 0 <= i < k - 1 && before == #[trigger] specificity(arg[i]);
                assert(now == specificity(arg[i]));
            }
        }
    }
}

/// `theorem_is_most_specific` ([`is_most_specific`]).
pub proof fn theorem_is_most_specific(arg: Seq<Complex>)
    ensures
        is_most_specific(arg),
{
    lemma_list_specificity(arg, arg.len() as int);
}

} // verus!

verus! {

/// [`nth_index_matches`] is §15.3.1's "any index i = An + B for any non-negative integer
/// n", as the spec's modelling choices say.
pub proof fn lemma_nth_index_matches(a: int, b: int, i: int)
    ensures
        nth_index_matches(a, b, i) <==> exists|n: int| n >= 0 && #[trigger] (a * n) + b == i,
{
    if a == 0 {
        if nth_index_matches(a, b, i) {
            assert(a * 0 + b == i);
        }
        if exists|n: int| n >= 0 && #[trigger] (a * n) + b == i {
            let n = choose|n: int| n >= 0 && #[trigger] (a * n) + b == i;
            assert(a * n == 0) by (nonlinear_arith)
                requires
                    a == 0,
            ;
        }
    } else if a > 0 {
        if nth_index_matches(a, b, i) {
            let n = (i - b) / a;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i - b, a);
            assert(a * n + b == i);
            assert(n >= 0) by (nonlinear_arith)
                requires
                    i - b >= 0,
                    a > 0,
                    n == (i - b) / a,
            ;
        }
        if exists|n: int| n >= 0 && #[trigger] (a * n) + b == i {
            let n = choose|n: int| n >= 0 && #[trigger] (a * n) + b == i;
            assert(a * n >= 0) by (nonlinear_arith)
                requires
                    a > 0,
                    n >= 0,
            ;
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(n, a);
            assert((n * a) % a == 0);
            assert(i - b == n * a) by (nonlinear_arith)
                requires
                    a * n + b == i,
            ;
        }
    } else {
        let m = -a;
        if nth_index_matches(a, b, i) {
            let n = (b - i) / m;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b - i, m);
            assert(n >= 0) by (nonlinear_arith)
                requires
                    b - i >= 0,
                    m > 0,
                    n == (b - i) / m,
            ;
            assert(a * n + b == i) by (nonlinear_arith)
                requires
                    m == -a,
                    b - i == m * n + (b - i) % m,
                    (b - i) % m == 0,
            ;
        }
        if exists|n: int| n >= 0 && #[trigger] (a * n) + b == i {
            let n = choose|n: int| n >= 0 && #[trigger] (a * n) + b == i;
            assert(m * n >= 0) by (nonlinear_arith)
                requires
                    m > 0,
                    n >= 0,
            ;
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(n, m);
            assert(b - i == n * m) by (nonlinear_arith)
                requires
                    a * n + b == i,
                    m == -a,
            ;
        }
    }
}

} // verus!
