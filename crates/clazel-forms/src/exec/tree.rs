//! Tree order, iteratively: a stack of (node, fuel) pairs, so that a deep
//! tree cannot overflow the call stack. The stack machine's state is
//! proven to be the spec's [`tree_order`] still to come.

use super::read::*;
#[cfg(verus_only)]
use crate::contract::*;
use crate::spec::*;
use clazel_dom::exec::Arena;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the stack of pending trees will still output: the tree order of
/// the top pair, then of the pair below it, and so on down. `sf[k]` is the
/// depth fuel of the tree rooted at `sn[k]`.
pub open spec fn stack_order(doc: Document, sn: Seq<NodeId>, sf: Seq<usize>) -> Seq<NodeId>
    recommends
        sn.len() == sf.len(),
    decreases sn.len(),
{
    if sn.len() == 0 || sf.len() != sn.len() {
        Seq::empty()
    } else {
        tree_order(doc, sn.last(), sf.last() as nat) + stack_order(doc, sn.drop_last(), sf.drop_last())
    }
}

/// Pushing a pair puts its tree first.
proof fn lemma_stack_order_push(doc: Document, sn: Seq<NodeId>, sf: Seq<usize>, c: NodeId, f: usize)
    requires
        sn.len() == sf.len(),
    ensures
        stack_order(doc, sn.push(c), sf.push(f)) == tree_order(doc, c, f as nat) + stack_order(doc, sn, sf),
{
    assert(sn.push(c).drop_last() =~= sn);
    assert(sf.push(f).drop_last() =~= sf);
    assert(sn.push(c).last() == c);
    assert(sf.push(f).last() == f);
}

/// [`tree_order`] of the tree below `root`, with the arena's size as fuel.
pub fn tree_order_exec(arena: &Arena, root: usize) -> (r: Vec<usize>)
    requires
        tree_order_requires(arena@, root),
    ensures
        tree_order_ensures(arena@, root, r@),
{
    let n = arena.len();
    let mut out: Vec<usize> = Vec::new();
    let mut sn: Vec<usize> = Vec::new();
    let mut sf: Vec<usize> = Vec::new();
    sn.push(root);
    sf.push(n);
    let ghost total = tree_order(arena@, root, n as nat);
    proof {
        assert(sn@.drop_last() =~= Seq::<usize>::empty());
        assert(sf@.drop_last() =~= Seq::<usize>::empty());
        assert(stack_order(arena@, Seq::empty(), Seq::empty()) =~= Seq::<NodeId>::empty());
        assert(out@ + stack_order(arena@, sn@, sf@) =~= total);
    }
    while sn.len() > 0
        invariant
            dom::wf(arena@),
            n == arena@.nodes.len(),
            sn.len() == sf.len(),
            forall|k: int| 0 <= k < sn.len() ==> dom::valid(arena@, #[trigger] sn@[k]),
            out@ + stack_order(arena@, sn@, sf@) == total,
        decreases total.len() - out.len(), sn.len(),
    {
        let ghost old_sn = sn@;
        let ghost old_sf = sf@;
        let top = sn.pop();
        let fuel = sf.pop();
        let (c, f) = match (top, fuel) {
            (Some(c), Some(f)) => (c, f),
            _ => {
                return out;
            },
        };
        proof {
            assert(sn@ =~= old_sn.drop_last());
            assert(sf@ =~= old_sf.drop_last());
            assert(c == old_sn.last());
            assert(f == old_sf.last());
            assert(dom::valid(arena@, c));
        }
        if f > 0 {
            out.push(c);
            let kids = arena.children(c);
            let ghost rest_sn = sn@;
            let ghost rest_sf = sf@;
            let fm: usize = f.saturating_sub(1);
            let mut j: usize = kids.len();
            proof {
                assert(kids@.skip(j as int) =~= Seq::<usize>::empty());
            }
            while j > 0
                invariant
                    dom::wf(arena@),
                    n == arena@.nodes.len(),
                    sn.len() == sf.len(),
                    dom::valid(arena@, c),
                    kids@ == arena@.nodes[c as int].children,
                    j <= kids.len(),
                    fm == f - 1,
                    forall|k: int| 0 <= k < sn.len() ==> dom::valid(arena@, #[trigger] sn@[k]),
                    stack_order(arena@, sn@, sf@) == forest_order(arena@, kids@.skip(j as int), fm as nat)
                        + stack_order(arena@, rest_sn, rest_sf),
                    rest_sn.len() == rest_sf.len(),
                decreases j,
            {
                let ghost before_sn = sn@;
                let ghost before_sf = sf@;
                // Never underflows: j > 0.
                j = j.saturating_sub(1);
                if let Some(k) = kids.get(j) {
                    let k = *k;
                    proof {
                        lemma_child_valid(arena@, c, j as int);
                    }
                    sn.push(k);
                    sf.push(fm);
                    proof {
                        lemma_stack_order_push(arena@, before_sn, before_sf, k, fm);
                        let ks = kids@.skip(j as int);
                        assert(ks[0] == kids@[j as int]);
                        assert(ks.drop_first() =~= kids@.skip(j as int + 1));
                    }
                }
            }
            proof {
                assert(kids@.skip(0) =~= kids@);
                assert(tree_order(arena@, c, f as nat) == seq![c] + forest_order(arena@, arena@.nodes[c as int].children, fm as nat));
                assert(old_sn.drop_last() =~= rest_sn);
                assert(old_sf.drop_last() =~= rest_sf);
                assert(stack_order(arena@, old_sn, old_sf) == tree_order(arena@, c, f as nat) + stack_order(
                    arena@,
                    rest_sn,
                    rest_sf,
                ));
                assert((out@).drop_last() + seq![c] =~= out@);
            }
        } else {
            proof {
                assert(tree_order(arena@, c, 0) =~= Seq::<NodeId>::empty());
                assert(stack_order(arena@, old_sn, old_sf) == tree_order(arena@, c, f as nat) + stack_order(
                    arena@,
                    sn@,
                    sf@,
                ));
                assert(Seq::<NodeId>::empty() + stack_order(arena@, sn@, sf@) =~= stack_order(arena@, sn@, sf@));
            }
        }
    }
    proof {
        assert(sn@.len() == 0);
        assert(stack_order(arena@, sn@, sf@) =~= Seq::<NodeId>::empty());
        assert(out@ + Seq::<NodeId>::empty() =~= out@);
    }
    out
}

} // verus!
