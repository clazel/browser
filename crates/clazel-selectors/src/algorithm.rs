//! The matching algorithm the exec code runs, as spec functions. [`super::spec`] says what
//! matching is: "match a complex selector against an element" tries every element the
//! rightmost combinator relates, and again for each of those, which takes time exponential in
//! the number of compound selectors. This is the same answer computed once per element and
//! compound selector, which `lemmas::theorem_match_total` proves equal to the spec and
//! bounded.
//!
//! For a complex selector of `n` compound selectors and an element `x`, it walks `x`'s
//! inclusive ancestors from the root down (the chain). For each element `s` it meets, its
//! row says, for each `i < n`, whether the first `i + 1` compound selectors match `s`. The
//! row of `s` needs only rows already computed: those of `s`'s parent (for `>`), of any
//! ancestor (for " ", kept as the "descendant" row: the rows of the ancestors, or-ed), of
//! the element before `s` (for `+`) and of every element before `s` (for `~`, kept as the
//! "earlier" row). When the selector has a sibling combinator, every element before each
//! chain node among its siblings gets a row; otherwise only the chain does. The answer is
//! the last entry of `x`'s row.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `x`'s inclusive ancestors, root first, following parents at most `fuel` times.
pub open spec fn chain_from(doc: Document, x: NodeId, fuel: nat) -> Seq<NodeId>
    decreases fuel,
{
    match parent_of(doc, x) {
        Some(p) => if fuel > 0 {
            chain_from(doc, p, (fuel - 1) as nat).push(x)
        } else {
            seq![x]
        },
        None => seq![x],
    }
}

/// `x`'s inclusive ancestors, root first.
pub open spec fn chain(doc: Document, x: NodeId) -> Seq<NodeId> {
    chain_from(doc, x, doc.nodes.len())
}

/// `n` falses.
pub open spec fn falses(n: nat) -> Seq<bool> {
    Seq::new(n, |i: int| false)
}

/// Two rows or-ed.
pub open spec fn or_rows(r1: Seq<bool>, r2: Seq<bool>) -> Seq<bool> {
    Seq::new(r1.len(), |i: int| r1[i] || r2[i])
}

/// True if the first `i + 1` compound selectors match an element that `combinator` relates
/// to the element at hand, given the rows of its parent, of its ancestors, of the element
/// before it and of all the elements before it.
pub open spec fn related(
    combinator: Combinator,
    i: int,
    parent: Seq<bool>,
    descendant: Seq<bool>,
    previous: Seq<bool>,
    earlier: Seq<bool>,
) -> bool {
    match combinator {
        Combinator::Descendant => descendant[i],
        Combinator::Child => parent[i],
        Combinator::NextSibling => previous[i],
        Combinator::SubsequentSibling => earlier[i],
    }
}

/// The row of `s`: entry `i` is true if the first `i + 1` compound selectors of `c` match
/// `s`. A node that is not an element has a row of falses.
pub open spec fn row(
    doc: Document,
    c: Complex,
    s: NodeId,
    parent: Seq<bool>,
    descendant: Seq<bool>,
    previous: Seq<bool>,
    earlier: Seq<bool>,
) -> Seq<bool> {
    Seq::new(
        c.compounds.len(),
        |i: int|
            is_element(doc, s) && compound_matches(
                doc,
                c.compounds[i],
                c.compounds[i].len() as int,
                s,
            ) && (i == 0 || related(c.combinators[i - 1], i - 1, parent, descendant, previous, earlier)),
    )
}

/// What the walk along a chain node's siblings carries.
pub ghost struct Siblings {
    /// The row of the last element so far ("+"), or falses.
    pub previous: Seq<bool>,
    /// The rows of the elements so far, or-ed ("~").
    pub earlier: Seq<bool>,
    /// How many entries of rows were computed: `n` for each element.
    pub work: nat,
}

/// The walk along the first `j` of `kids`, the children of a node whose row is `parent`, with
/// the descendant row `descendant` that every child shares.
pub open spec fn siblings_loop(
    doc: Document,
    c: Complex,
    kids: Seq<NodeId>,
    j: int,
    parent: Seq<bool>,
    descendant: Seq<bool>,
) -> Siblings
    decreases j,
{
    let n = c.compounds.len();
    if j <= 0 || j > kids.len() {
        Siblings { previous: falses(n), earlier: falses(n), work: 0 }
    } else {
        let before = siblings_loop(doc, c, kids, j - 1, parent, descendant);
        let s = kids[j - 1];
        if is_element(doc, s) {
            let r = row(doc, c, s, parent, descendant, before.previous, before.earlier);
            Siblings { previous: r, earlier: or_rows(before.earlier, r), work: before.work + n }
        } else {
            before
        }
    }
}

/// The state at a chain node: its row, its descendant row, and the work so far.
pub ghost struct Level {
    /// The node's row.
    pub row: Seq<bool>,
    /// The rows of its ancestors, or-ed.
    pub descendant: Seq<bool>,
    /// How many entries of rows were computed down to here.
    pub work: nat,
}

/// The state at node `k` of the chain `ch`. `siblings` says whether the selector has a
/// sibling combinator, so that the elements before each chain node need rows.
pub open spec fn level(doc: Document, c: Complex, ch: Seq<NodeId>, k: int, siblings: bool) -> Level
    decreases k,
{
    let n = c.compounds.len();
    if k <= 0 {
        // The root of the chain has no parent, and so no ancestors and no other siblings.
        Level {
            row: row(doc, c, ch[0], falses(n), falses(n), falses(n), falses(n)),
            descendant: falses(n),
            work: n,
        }
    } else {
        let up = level(doc, c, ch, k - 1, siblings);
        let descendant = or_rows(up.row, up.descendant);
        if siblings {
            let kids = children_of(doc, ch[k - 1]);
            let walk = siblings_loop(
                doc,
                c,
                kids,
                clazel_dom::spec::index_of(kids, ch[k]),
                up.row,
                descendant,
            );
            Level {
                row: row(doc, c, ch[k], up.row, descendant, walk.previous, walk.earlier),
                descendant,
                work: up.work + walk.work + n,
            }
        } else {
            Level {
                row: row(doc, c, ch[k], up.row, descendant, falses(n), falses(n)),
                descendant,
                work: up.work + n,
            }
        }
    }
}

/// True if one of the first `k` combinators of `c` is `+` or `~`.
pub open spec fn sibling_combinator_within(c: Complex, k: int) -> bool
    decreases k,
{
    if k <= 0 || k > c.combinators.len() {
        false
    } else {
        c.combinators[k - 1] == Combinator::NextSibling || c.combinators[k - 1]
            == Combinator::SubsequentSibling || sibling_combinator_within(c, k - 1)
    }
}

/// True if `c` has a `+` or `~` combinator.
pub open spec fn uses_siblings(c: Complex) -> bool {
    sibling_combinator_within(c, c.combinators.len() as int)
}

/// The algorithm: whether `c` matches `x`, and how many entries of rows it computed.
pub open spec fn dp_match(doc: Document, c: Complex, x: NodeId) -> (bool, nat) {
    let ch = chain(doc, x);
    let top = level(doc, c, ch, ch.len() - 1, uses_siblings(c));
    (top.row[c.compounds.len() - 1], top.work)
}

} // verus!
