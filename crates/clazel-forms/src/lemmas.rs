//! Facts proven about [`crate::spec`]. They are evidence that the
//! transcription is right and the bridge the implementation uses (every
//! node of a tree order is in the tree of its root; "connected" is "the root
//! is the document"), not part of what the implementation must meet.

#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use clazel_dom::lemmas::*;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first element of `order` with ID `id`, if any, is an element of
/// `order` with that ID.
pub proof fn lemma_first_with_id(doc: Document, order: Seq<NodeId>, id: Seq<u32>, x: NodeId)
    requires
        first_with_id(doc, order, id) == Some(x),
    ensures
        order.contains(x),
        is_element(doc, x),
        element_id(doc, x) == Some(id),
    decreases order.len(),
{
    if order.len() > 0 && is_element(doc, order[0]) && element_id(doc, order[0]) == Some(id) {
        assert(order[0] == x);
    } else {
        lemma_first_with_id(doc, order.drop_first(), id, x);
        assert(order.drop_first().contains(x));
        let k = choose|k: int| 0 <= k < order.drop_first().len() && order.drop_first()[k] == x;
        assert(order[k + 1] == x);
    }
}

/// Walking up from `x` for `fuel` steps (with `fuel + 1` at least the
/// length of its path) reaches the first node of its path.
pub proof fn lemma_root_is_path_head(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId, fuel: nat)
    requires
        dom::wf_with(doc, paths),
        dom::valid(doc, x),
        fuel + 1 >= paths[x as int].len(),
    ensures
        root_within(doc, x, fuel) == paths[x as int][0],
    decreases fuel,
{
    lemma_path(doc, paths, x);
    let px = paths[x as int];
    assert(px == match doc.nodes[x as int].parent {
        None => seq![x],
        Some(p) => paths[p as int].push(x),
    });
    match doc.nodes[x as int].parent {
        None => {},
        Some(p) => {
            assert(p < doc.nodes.len());
            let pp = paths[p as int];
            lemma_path(doc, paths, p);
            assert(px.len() == pp.len() + 1);
            assert(fuel > 0);
            lemma_root_is_path_head(doc, paths, p, (fuel - 1) as nat);
            assert(px[0] == pp[0]);
        },
    }
}

/// `root` is the first node of the path, and has no parent.
pub proof fn lemma_root_facts(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId)
    requires
        dom::wf_with(doc, paths),
        dom::valid(doc, x),
    ensures
        root(doc, x) == paths[x as int][0],
        dom::valid(doc, root(doc, x)),
        paths[root(doc, x) as int] == seq![root(doc, x)],
{
    lemma_path_facts(doc, paths, x);
    lemma_root_is_path_head(doc, paths, x, doc.nodes.len());
    lemma_path(doc, paths, x);
    let r = paths[x as int][0];
    assert(paths[r as int] == paths[x as int].subrange(0, 1));
    assert(paths[x as int].subrange(0, 1) =~= seq![r]);
}

/// Every node of the tree order of `r` has the first node of `r`'s path
/// first on its own path, and is a node of the arena.
pub proof fn lemma_tree_head(doc: Document, paths: Seq<Seq<NodeId>>, r: NodeId, f: nat, e: NodeId)
    requires
        dom::wf_with(doc, paths),
        dom::valid(doc, r),
        tree_order(doc, r, f).contains(e),
    ensures
        dom::valid(doc, e),
        paths[e as int][0] == paths[r as int][0],
    decreases f, 0nat,
{
    lemma_path(doc, paths, r);
    if f > 0 {
        let kids = doc.nodes[r as int].children;
        assert(tree_order(doc, r, f) == seq![r] + forest_order(doc, kids, (f - 1) as nat));
        if e != r {
            assert(forest_order(doc, kids, (f - 1) as nat).contains(e));
            lemma_forest_head(doc, paths, r, kids, (f - 1) as nat, e);
        }
    }
}

/// [`lemma_tree_head`] for a list of children of `r`.
pub proof fn lemma_forest_head(
    doc: Document,
    paths: Seq<Seq<NodeId>>,
    r: NodeId,
    kids: Seq<NodeId>,
    f: nat,
    e: NodeId,
)
    requires
        dom::wf_with(doc, paths),
        dom::valid(doc, r),
        forall|k: int| 0 <= k < kids.len() ==> doc.nodes[r as int].children.contains(#[trigger] kids[k]),
        forest_order(doc, kids, f).contains(e),
    ensures
        dom::valid(doc, e),
        paths[e as int][0] == paths[r as int][0],
    decreases f, kids.len(),
{
    lemma_path(doc, paths, r);
    if kids.len() > 0 {
        let c = kids[0];
        assert(doc.nodes[r as int].children.contains(c));
        let k = choose|k: int| 0 <= k < doc.nodes[r as int].children.len() && doc.nodes[r as int].children[k] == c;
        assert(dom::valid(doc, c));
        assert(doc.nodes[c as int].parent == Some(r));
        lemma_path(doc, paths, c);
        assert(paths[c as int] == paths[r as int].push(c));
        assert(forest_order(doc, kids, f) == tree_order(doc, c, f) + forest_order(doc, kids.drop_first(), f));
        if tree_order(doc, c, f).contains(e) {
            lemma_tree_head(doc, paths, c, f, e);
            assert(paths[c as int][0] == paths[r as int][0]);
        } else {
            assert(forest_order(doc, kids.drop_first(), f).contains(e));
            assert forall|k: int| 0 <= k < kids.drop_first().len() implies doc.nodes[r as int].children.contains(
                #[trigger] kids.drop_first()[k],
            ) by {
                assert(kids.drop_first()[k] == kids[k + 1]);
            }
            lemma_forest_head(doc, paths, r, kids.drop_first(), f, e);
        }
    }
}

/// Every node of the tree order of the root of `form` has the root of
/// `form` as its root, is a node of the arena, and is connected exactly
/// when that root is the document node.
pub proof fn lemma_in_order(doc: Document, form: NodeId, e: NodeId)
    requires
        dom::wf(doc),
        dom::valid(doc, form),
        tree_order(doc, root(doc, form), doc.nodes.len()).contains(e),
    ensures
        dom::valid(doc, e),
        root(doc, e) == root(doc, form),
        dom::connected(doc, e) == (root(doc, form) == 0),
{
    let paths = lemma_wf_witness(doc);
    lemma_root_facts(doc, paths, form);
    let r = root(doc, form);
    lemma_tree_head(doc, paths, r, doc.nodes.len(), e);
    lemma_root_facts(doc, paths, e);
    assert(paths[e as int][0] == paths[r as int][0]);
    assert(paths[r as int][0] == r);
    // connected: 0 is on e's path iff it heads it.
    lemma_ancestor_iff_path(doc, paths, 0, e);
    lemma_path(doc, paths, e);
    if paths[e as int].contains(0) {
        lemma_path_prefix(doc, paths, 0, e);
        assert(doc.nodes[0].parent is None);
        assert(paths[0] == seq![0 as NodeId]);
        let k = choose|k: int|
            0 <= k < paths[e as int].len() && paths[e as int][k] == 0 && paths[0] == paths[e as int].subrange(0, k + 1);
        assert(paths[0].len() == 1);
        assert(k == 0);
    }
}

/// Every control of a form is a submittable element (so a node).
pub proof fn lemma_controls_members(doc: Document, form: NodeId, order: Seq<NodeId>, c: NodeId)
    requires
        controls_in(doc, form, order).contains(c),
    ensures
        is_submittable(doc, c),
    decreases order.len(),
{
    if order.len() > 0 {
        if controls_in(doc, form, order.drop_last()).contains(c) {
            lemma_controls_members(doc, form, order.drop_last(), c);
        } else {
            assert(is_control_of(doc, form, order.last()));
            assert(c == order.last());
        }
    }
}

/// What the implementation computes once per form, to decide whether a
/// control's `form` attribute names `form`: `form`'s ID, if `form` is a
/// `form` element and the first element of `order` with that ID.
pub open spec fn fid_value(doc: Document, order: Seq<NodeId>, form: NodeId) -> Option<Seq<u32>> {
    if is_html(doc, form, b"form"@) && element_id(doc, form) is Some && first_with_id(
        doc,
        order,
        element_id(doc, form)->Some_0,
    ) == Some(form) {
        element_id(doc, form)
    } else {
        None
    }
}

/// A `form` attribute value `a` names `form` (the first element of
/// `order` with ID `a` is a `form`, and is `form`) exactly when
/// [`fid_value`] is `a`.
pub proof fn lemma_fid(doc: Document, order: Seq<NodeId>, form: NodeId, a: Seq<u32>)
    ensures
        (match first_with_id(doc, order, a) {
            Some(f) => if is_html(doc, f, b"form"@) {
                Some(f)
            } else {
                None
            },
            None => None,
        } == Some(form)) == (fid_value(doc, order, form) == Some(a)),
{
    if let Some(f) = first_with_id(doc, order, a) {
        lemma_first_with_id(doc, order, a, f);
    }
    if fid_value(doc, order, form) == Some(a) {
        assert(element_id(doc, form) == Some(a));
    }
}

} // verus!
