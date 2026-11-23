//! A `select`'s "list of options" (HTML §4.10.7), as an explicit-stack walk
//! that visits every node the standard's loop visits (skipping the
//! descendants of the nodes it says to skip) and keeps the `option`s.

use super::read::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::lemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
use clazel_dom::exec::Arena;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The standard's "node is a `select`, `hr`, `option`, `datalist`, or an
/// `optgroup` with an `optgroup` ancestor in between" (`in_group`).
pub open spec fn stops(doc: Document, c: NodeId, in_group: bool) -> bool {
    is_html(doc, c, b"select"@) || is_html(doc, c, b"hr"@) || is_html(doc, c, b"option"@) || is_html(
        doc,
        c,
        b"datalist"@,
    ) || (is_html(doc, c, b"optgroup"@) && in_group)
}

/// Every node [`options_in`] visits, in order, options or not.
pub open spec fn walk_in(doc: Document, kids: Seq<NodeId>, in_group: bool, fuel: nat) -> Seq<NodeId>
    decreases fuel, kids.len(),
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        walk_one(doc, kids[0], in_group, fuel) + walk_in(doc, kids.drop_first(), in_group, fuel)
    }
}

/// The node `c` and, unless it stops the walk, the nodes visited below it.
pub open spec fn walk_one(doc: Document, c: NodeId, in_group: bool, fuel: nat) -> Seq<NodeId>
    decreases fuel, 0nat,
{
    seq![c] + if stops(doc, c, in_group) || fuel == 0 {
        Seq::empty()
    } else {
        walk_in(
            doc,
            doc.nodes[c as int].children,
            in_group || is_html(doc, c, b"optgroup"@),
            (fuel - 1) as nat,
        )
    }
}

/// The `option` elements of `s`, in order.
pub open spec fn only_options(doc: Document, s: Seq<NodeId>) -> Seq<NodeId>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        only_options(doc, s.drop_last()) + if is_html(doc, s.last(), b"option"@) {
            seq![s.last()]
        } else {
            Seq::empty()
        }
    }
}

/// Filtering by "is an option" distributes over concatenation.
proof fn lemma_only_options_append(doc: Document, a: Seq<NodeId>, b: Seq<NodeId>)
    ensures
        only_options(doc, a + b) == only_options(doc, a) + only_options(doc, b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_only_options_append(doc, a, b.drop_last());
        assert(only_options(doc, b) == only_options(doc, b.drop_last()) + if is_html(doc, b.last(), b"option"@) {
            seq![b.last()]
        } else {
            Seq::empty()
        });
    }
}

/// The spec's [`options_in`] is the options among the nodes visited.
pub proof fn lemma_options_in_is_filter(doc: Document, kids: Seq<NodeId>, in_group: bool, fuel: nat)
    ensures
        options_in(doc, kids, in_group, fuel) == only_options(doc, walk_in(doc, kids, in_group, fuel)),
    decreases fuel, kids.len(),
{
    if kids.len() > 0 {
        let c = kids[0];
        let below_o = if stops(doc, c, in_group) || fuel == 0 {
            Seq::<NodeId>::empty()
        } else {
            options_in(
                doc,
                doc.nodes[c as int].children,
                in_group || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
            )
        };
        let below_w = if stops(doc, c, in_group) || fuel == 0 {
            Seq::<NodeId>::empty()
        } else {
            walk_in(
                doc,
                doc.nodes[c as int].children,
                in_group || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
            )
        };
        if !(stops(doc, c, in_group) || fuel == 0) {
            lemma_options_in_is_filter(
                doc,
                doc.nodes[c as int].children,
                in_group || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
            );
        }
        lemma_options_in_is_filter(doc, kids.drop_first(), in_group, fuel);
        let here_w = seq![c];
        assert(walk_one(doc, c, in_group, fuel) == here_w + below_w);
        assert(walk_in(doc, kids, in_group, fuel) == (here_w + below_w) + walk_in(doc, kids.drop_first(), in_group, fuel));
        assert(only_options(doc, Seq::<NodeId>::empty()) == Seq::<NodeId>::empty());
        lemma_only_options_append(doc, here_w + below_w, walk_in(doc, kids.drop_first(), in_group, fuel));
        lemma_only_options_append(doc, here_w, below_w);
        assert(only_options(doc, here_w) == if is_html(doc, c, b"option"@) {
            seq![c]
        } else {
            Seq::empty()
        }) by {
            assert(here_w.drop_last() =~= Seq::<NodeId>::empty());
        }
    }
}

/// Concatenation bookkeeping of the walk's loop invariant.
proof fn lemma_push_assoc(a: Seq<NodeId>, c: NodeId, w: Seq<NodeId>, r: Seq<NodeId>)
    ensures
        a.push(c) + w + r == a + (seq![c] + w + r),
{
    assert(a.push(c) + w + r =~= a + (seq![c] + w + r));
}

/// What a stack of pending (node, fuel, in-group) frames will still
/// visit: the top frame's nodes, then the frame below's, and so on.
pub open spec fn stack_walk(doc: Document, sn: Seq<NodeId>, sf: Seq<usize>, sg: Seq<bool>) -> Seq<NodeId>
    decreases sn.len(),
{
    if sn.len() == 0 || sf.len() != sn.len() || sg.len() != sn.len() {
        Seq::empty()
    } else {
        walk_one(doc, sn.last(), sg.last(), sf.last() as nat) + stack_walk(
            doc,
            sn.drop_last(),
            sf.drop_last(),
            sg.drop_last(),
        )
    }
}

/// Pushing a frame puts its walk first.
proof fn lemma_stack_walk_push(
    doc: Document,
    sn: Seq<NodeId>,
    sf: Seq<usize>,
    sg: Seq<bool>,
    c: NodeId,
    f: usize,
    g: bool,
)
    requires
        sn.len() == sf.len(),
        sn.len() == sg.len(),
    ensures
        stack_walk(doc, sn.push(c), sf.push(f), sg.push(g)) == walk_one(doc, c, g, f as nat) + stack_walk(
            doc,
            sn,
            sf,
            sg,
        ),
{
    assert(sn.push(c).drop_last() =~= sn);
    assert(sf.push(f).drop_last() =~= sf);
    assert(sg.push(g).drop_last() =~= sg);
    assert(sn.push(c).last() == c);
    assert(sf.push(f).last() == f);
    assert(sg.push(g).last() == g);
}

/// [`stops`].
pub fn stops_exec(arena: &Arena, c: usize, in_group: bool) -> (r: bool)
    requires
        dom::valid(arena@, c),
    ensures
        r == stops(arena@, c, in_group),
{
    is_html_exec(arena, c, b"select") || is_html_exec(arena, c, b"hr") || is_html_exec(arena, c, b"option")
        || is_html_exec(arena, c, b"datalist") || (in_group && is_html_exec(arena, c, b"optgroup"))
}

/// Push the children of `c`, last first, with fuel `f` and flag `ig`.
pub fn push_children(
    arena: &Arena,
    c: usize,
    f: usize,
    ig: bool,
    sn: &mut Vec<usize>,
    sf: &mut Vec<usize>,
    sg: &mut Vec<bool>,
)
    requires
        dom::wf(arena@),
        dom::valid(arena@, c),
        old(sn).len() == old(sf).len(),
        old(sn).len() == old(sg).len(),
        forall|k: int| 0 <= k < old(sn).len() ==> dom::valid(arena@, #[trigger] old(sn)@[k]),
    ensures
        final(sn).len() == final(sf).len(),
        final(sn).len() == final(sg).len(),
        forall|k: int| 0 <= k < final(sn).len() ==> dom::valid(arena@, #[trigger] final(sn)@[k]),
        stack_walk(arena@, final(sn)@, final(sf)@, final(sg)@) == walk_in(
            arena@,
            arena@.nodes[c as int].children,
            ig,
            f as nat,
        ) + stack_walk(arena@, old(sn)@, old(sf)@, old(sg)@),
{
    let kids = arena.children(c);
    let ghost rest_sn = sn@;
    let ghost rest_sf = sf@;
    let ghost rest_sg = sg@;
    let mut j: usize = kids.len();
    proof {
        assert(kids@.skip(j as int) =~= Seq::<usize>::empty());
    }
    while j > 0
        invariant
            dom::wf(arena@),
            dom::valid(arena@, c),
            kids@ == arena@.nodes[c as int].children,
            j <= kids.len(),
            sn.len() == sf.len(),
            sn.len() == sg.len(),
            rest_sn.len() == rest_sf.len(),
            rest_sn.len() == rest_sg.len(),
            forall|k: int| 0 <= k < sn.len() ==> dom::valid(arena@, #[trigger] sn@[k]),
            stack_walk(arena@, sn@, sf@, sg@) == walk_in(arena@, kids@.skip(j as int), ig, f as nat) + stack_walk(
                arena@,
                rest_sn,
                rest_sf,
                rest_sg,
            ),
        decreases j,
    {
        let ghost before_sn = sn@;
        let ghost before_sf = sf@;
        let ghost before_sg = sg@;
        // Never underflows: j > 0.
        j = j.saturating_sub(1);
        if let Some(k) = kids.get(j) {
            let k = *k;
            proof {
                lemma_child_valid(arena@, c, j as int);
            }
            sn.push(k);
            sf.push(f);
            sg.push(ig);
            proof {
                lemma_stack_walk_push(arena@, before_sn, before_sf, before_sg, k, f, ig);
                let ks = kids@.skip(j as int);
                assert(ks.len() > 0);
                assert(ks[0] == kids@[j as int]);
                assert(ks.drop_first() =~= kids@.skip(j as int + 1));
                assert(walk_in(arena@, ks, ig, f as nat) == walk_one(arena@, k, ig, f as nat) + walk_in(
                    arena@,
                    ks.drop_first(),
                    ig,
                    f as nat,
                ));
                assert(sn@ =~= before_sn.push(k));
                assert forall|m: int| 0 <= m < sn.len() implies dom::valid(arena@, #[trigger] sn@[m]) by {
                    if m < before_sn.len() {
                        assert(sn@[m] == before_sn[m]);
                    } else {
                        assert(sn@[m] == k);
                    }
                }
            }
        }
    }
    proof {
        assert(kids@.skip(0) =~= kids@);
    }
}

/// Every node [`options_in`] visits below the children of `sel`, in order.
pub fn walk_options(arena: &Arena, sel: usize) -> (r: Vec<usize>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, sel),
    ensures
        r@ == walk_in(arena@, arena@.nodes[sel as int].children, false, arena@.nodes.len()),
{
    let n = arena.len();
    let mut out: Vec<usize> = Vec::new();
    let mut sn: Vec<usize> = Vec::new();
    let mut sf: Vec<usize> = Vec::new();
    let mut sg: Vec<bool> = Vec::new();
    push_children(arena, sel, n, false, &mut sn, &mut sf, &mut sg);
    let ghost total = walk_in(arena@, arena@.nodes[sel as int].children, false, n as nat);
    proof {
        assert(stack_walk(arena@, Seq::empty(), Seq::empty(), Seq::empty()) =~= Seq::<NodeId>::empty());
        assert(total + Seq::<NodeId>::empty() =~= total);
        assert(out@ + stack_walk(arena@, sn@, sf@, sg@) =~= total);
    }
    while !sn.is_empty()
        invariant
            dom::wf(arena@),
            n == arena@.nodes.len(),
            sn.len() == sf.len(),
            sn.len() == sg.len(),
            forall|k: int| 0 <= k < sn.len() ==> dom::valid(arena@, #[trigger] sn@[k]),
            out@ + stack_walk(arena@, sn@, sf@, sg@) == total,
        decreases total.len() - out.len(),
    {
        let ghost old_sn = sn@;
        let ghost old_sf = sf@;
        let ghost old_sg = sg@;
        let top = sn.pop();
        let fuel = sf.pop();
        let flag = sg.pop();
        let (c, f, ig) = match (top, fuel, flag) {
            (Some(c), Some(f), Some(g)) => (c, f, g),
            _ => {
                return out;
            },
        };
        proof {
            assert(sn@ =~= old_sn.drop_last());
            assert(sf@ =~= old_sf.drop_last());
            assert(sg@ =~= old_sg.drop_last());
            assert(c == old_sn.last());
            assert(f == old_sf.last());
            assert(ig == old_sg.last());
            assert(dom::valid(arena@, c));
        }
        let ghost rest_sn = sn@;
        let ghost rest_sf = sf@;
        let ghost rest_sg = sg@;
        let ghost before = out@;
        out.push(c);
        let stopped = stops_exec(arena, c, ig);
        proof {
            assert(out@ =~= before.push(c));
            assert(stack_walk(arena@, old_sn, old_sf, old_sg) == walk_one(arena@, c, ig, f as nat) + stack_walk(
                arena@,
                rest_sn,
                rest_sf,
                rest_sg,
            ));
        }
        if !stopped && f > 0 {
            let ig2 = ig || is_html_exec(arena, c, b"optgroup");
            let fm: usize = f.saturating_sub(1);
            push_children(arena, c, fm, ig2, &mut sn, &mut sf, &mut sg);
            proof {
                assert(walk_one(arena@, c, ig, f as nat) == seq![c] + walk_in(
                    arena@,
                    arena@.nodes[c as int].children,
                    ig2,
                    fm as nat,
                ));
                assert(before + stack_walk(arena@, old_sn, old_sf, old_sg) == total);
                lemma_push_assoc(
                    before,
                    c,
                    walk_in(arena@, arena@.nodes[c as int].children, ig2, fm as nat),
                    stack_walk(arena@, rest_sn, rest_sf, rest_sg),
                );
            }
        } else {
            proof {
                assert(walk_one(arena@, c, ig, f as nat) == seq![c]);
                lemma_push_assoc(before, c, Seq::empty(), stack_walk(arena@, rest_sn, rest_sf, rest_sg));
                assert(seq![c] + Seq::<NodeId>::empty() + stack_walk(arena@, rest_sn, rest_sf, rest_sg) =~= seq![c] + stack_walk(arena@, rest_sn, rest_sf, rest_sg));
            }
        }
    }
    proof {
        assert(sn@.len() == 0);
        assert(stack_walk(arena@, sn@, sf@, sg@) =~= Seq::<NodeId>::empty());
        assert(out@ + Seq::<NodeId>::empty() =~= out@);
    }
    out
}

/// [`list_of_options`] of `sel`.
pub fn list_of_options_exec(arena: &Arena, sel: usize) -> (r: Vec<usize>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, sel),
    ensures
        r@ == list_of_options(arena@, sel),
{
    let visited = walk_options(arena, sel);
    let ghost vis = visited@;
    proof {
        lemma_options_in_is_filter(
            arena@,
            arena@.nodes[sel as int].children,
            false,
            arena@.nodes.len(),
        );
        assert forall|k: int| 0 <= k < arena@.nodes[sel as int].children.len() implies dom::valid(
            arena@,
            #[trigger] arena@.nodes[sel as int].children[k],
        ) by {
            lemma_child_valid(arena@, sel, k);
        }
        assert forall|k: int| 0 <= k < vis.len() implies dom::valid(arena@, #[trigger] vis[k]) by {
            lemma_walk_valid(arena@, arena@.nodes[sel as int].children, false, arena@.nodes.len(), vis[k]);
        }
        assert(vis.subrange(0, 0) =~= Seq::<usize>::empty());
    }
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < visited.len()
        invariant
            i <= visited.len(),
            visited@ == vis,
            dom::wf(arena@),
            forall|k: int| 0 <= k < vis.len() ==> dom::valid(arena@, #[trigger] vis[k]),
            out@ == only_options(arena@, vis.subrange(0, i as int)),
        decreases visited.len() - i,
    {
        if let Some(c) = visited.get(i) {
            let c = *c;
            let ghost before = out@;
            proof {
                assert(vis.subrange(0, i as int + 1).drop_last() =~= vis.subrange(0, i as int));
                assert(vis.subrange(0, i as int + 1).last() == vis[i as int]);
            }
            if is_html_exec(arena, c, b"option") {
                out.push(c);
                proof {
                    assert(out@ =~= before.push(c));
                }
            }
        }
        // Never saturates: i < visited.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(vis.subrange(0, vis.len() as int) =~= vis);
    }
    out
}

/// Every element of [`only_options`] is an HTML `option`.
pub proof fn lemma_only_options_members(doc: Document, s: Seq<NodeId>, e: NodeId)
    requires
        only_options(doc, s).contains(e),
    ensures
        is_html(doc, e, b"option"@),
    decreases s.len(),
{
    if s.len() > 0 {
        if only_options(doc, s.drop_last()).contains(e) {
            lemma_only_options_members(doc, s.drop_last(), e);
        } else {
            assert(is_html(doc, s.last(), b"option"@));
            assert(e == s.last());
        }
    }
}

/// Every node [`walk_in`] visits is a node of the arena.
pub proof fn lemma_walk_valid(doc: Document, kids: Seq<NodeId>, ig: bool, fuel: nat, e: NodeId)
    requires
        dom::wf(doc),
        forall|k: int| 0 <= k < kids.len() ==> dom::valid(doc, #[trigger] kids[k]),
        walk_in(doc, kids, ig, fuel).contains(e),
    ensures
        dom::valid(doc, e),
    decreases fuel, kids.len(),
{
    assert(kids.len() > 0) by {
        assert(walk_in(doc, kids, ig, fuel).len() > 0);
    }
    let c = kids[0];
    assert(dom::valid(doc, c));
    let w = walk_one(doc, c, ig, fuel);
    if w.contains(e) {
        if e != c {
            let below = walk_in(
                doc,
                doc.nodes[c as int].children,
                ig || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
            );
            assert(below.contains(e));
            assert forall|k: int| 0 <= k < doc.nodes[c as int].children.len() implies dom::valid(
                doc,
                #[trigger] doc.nodes[c as int].children[k],
            ) by {
                lemma_child_valid(doc, c, k);
            }
            lemma_walk_valid(
                doc,
                doc.nodes[c as int].children,
                ig || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
                e,
            );
        }
    } else {
        assert forall|k: int| 0 <= k < kids.drop_first().len() implies dom::valid(
            doc,
            #[trigger] kids.drop_first()[k],
        ) by {
            assert(kids.drop_first()[k] == kids[k + 1]);
        }
        lemma_walk_valid(doc, kids.drop_first(), ig, fuel, e);
    }
}

} // verus!
