//! Phase 7 item 7.13's theorems: the operations of `spec.rs`'s "mutation
//! algorithms scripts call" keep the arena well formed ([`wf`]) and do
//! what their DOM steps say. [`super::lemmas`] has the theorems of the
//! parser's operations, and the machinery (witness paths, `attach`) these
//! build on.
//!
//! Each `theorem_*` listed in `Cargo.toml` is a `pub proof fn` here.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Attribute changes

/// Setting an element's attribute list keeps the arena well formed and
/// changes nothing else: the element's other kind fields, parent, children
/// and wrapper, every other node and the arena's length are kept.
pub proof fn lemma_set_attributes_wf(doc: Document, e: NodeId, attrs: Seq<Attr>)
    requires
        wf(doc),
        valid(doc, e),
        doc.nodes[e as int].kind is Element,
    ensures
        wf(set_attributes(doc, e, attrs)),
        set_attributes(doc, e, attrs).nodes.len() == doc.nodes.len(),
        ({
            let old = doc.nodes[e as int];
            let new = set_attributes(doc, e, attrs).nodes[e as int];
            &&& new.kind is Element
            &&& new.kind->Element_attributes == attrs
            &&& new.kind->Element_namespace == old.kind->Element_namespace
            &&& new.kind->Element_prefix == old.kind->Element_prefix
            &&& new.kind->Element_local_name == old.kind->Element_local_name
            &&& new.kind->Element_template_contents == old.kind->Element_template_contents
            &&& new.kind->Element_form_owner == old.kind->Element_form_owner
            &&& new.parent == old.parent
            &&& new.children == old.children
            &&& new.wrapper == old.wrapper
        }),
        forall|i: int| 0 <= i < doc.nodes.len() && i != e ==> #[trigger] set_attributes(doc, e, attrs).nodes[i] == doc.nodes[i],
{
    let paths = lemma_wf_witness(doc);
    let k = set_attributes(doc, e, attrs).nodes[e as int].kind;
    assert(set_attributes(doc, e, attrs) == set_kind(doc, e, k));
    lemma_set_kind_wf(doc, paths, e, k);
}

/// DOM §4.9† "change an attribute" keeps the arena well formed; the
/// attribute is the same but for its value, which is `value`, and every
/// other attribute is as it was.
pub proof fn theorem_change_attribute_wf(doc: Document, e: NodeId, i: nat, value: Seq<u32>)
    requires
        attribute_requires(doc, e, i),
    ensures
        wf(change_attribute(doc, e, i, value)),
        change_attribute(doc, e, i, value).nodes.len() == doc.nodes.len(),
        ({
            let old = doc.nodes[e as int].kind->Element_attributes;
            let new = change_attribute(doc, e, i, value).nodes[e as int].kind->Element_attributes;
            &&& new.len() == old.len()
            &&& new[i as int] == (Attr { value, ..old[i as int] })
            &&& forall|j: int| 0 <= j < old.len() && j != i ==> #[trigger] new[j] == old[j]
        }),
        change_attribute(doc, e, i, value).nodes[e as int].kind is Element,
        forall|j: int| 0 <= j < doc.nodes.len() && j != e ==> #[trigger] change_attribute(doc, e, i, value).nodes[j] == doc.nodes[j],
{
    let attrs = doc.nodes[e as int].kind->Element_attributes;
    lemma_set_attributes_wf(doc, e, attrs.update(i as int, Attr { value, ..attrs[i as int] }));
}

/// DOM §4.9† "remove an attribute" keeps the arena well formed; the
/// element's attribute list is its old one without the `i`th.
pub proof fn theorem_remove_attribute_wf(doc: Document, e: NodeId, i: nat)
    requires
        attribute_requires(doc, e, i),
    ensures
        wf(remove_attribute(doc, e, i)),
        remove_attribute(doc, e, i).nodes.len() == doc.nodes.len(),
        remove_attribute(doc, e, i).nodes[e as int].kind is Element,
        remove_attribute(doc, e, i).nodes[e as int].kind->Element_attributes == doc.nodes[e as int].kind->Element_attributes.remove(i as int),
        remove_attribute(doc, e, i).nodes[e as int].kind->Element_attributes.len() + 1 == doc.nodes[e as int].kind->Element_attributes.len(),
        forall|j: int| 0 <= j < doc.nodes.len() && j != e ==> #[trigger] remove_attribute(doc, e, i).nodes[j] == doc.nodes[j],
{
    lemma_set_attributes_wf(doc, e, doc.nodes[e as int].kind->Element_attributes.remove(i as int));
}

/// DOM §4.9† "replace an attribute" keeps the arena well formed; the
/// `i`th attribute of the element's list is `new_attr` and the others are
/// as they were.
pub proof fn theorem_replace_attribute_wf(doc: Document, e: NodeId, i: nat, new_attr: Attr)
    requires
        attribute_requires(doc, e, i),
    ensures
        wf(replace_attribute(doc, e, i, new_attr)),
        replace_attribute(doc, e, i, new_attr).nodes.len() == doc.nodes.len(),
        replace_attribute(doc, e, i, new_attr).nodes[e as int].kind is Element,
        ({
            let old = doc.nodes[e as int].kind->Element_attributes;
            let new = replace_attribute(doc, e, i, new_attr).nodes[e as int].kind->Element_attributes;
            &&& new.len() == old.len()
            &&& new[i as int] == new_attr
            &&& forall|j: int| 0 <= j < old.len() && j != i ==> #[trigger] new[j] == old[j]
        }),
        forall|j: int| 0 <= j < doc.nodes.len() && j != e ==> #[trigger] replace_attribute(doc, e, i, new_attr).nodes[j] == doc.nodes[j],
{
    lemma_set_attributes_wf(doc, e, doc.nodes[e as int].kind->Element_attributes.update(i as int, new_attr));
}

// ---------------------------------------------------------------------
// adopt

/// DOM §4.5 "adopt" keeps the arena well formed and leaves the node
/// without a parent; no kind changes, no other node's parent changes.
pub proof fn theorem_adopt_wf(doc: Document, node: NodeId)
    requires
        adopt_requires(doc, node),
    ensures
        wf(adopt(doc, node)),
        adopt(doc, node).nodes.len() == doc.nodes.len(),
        adopt(doc, node).nodes[node as int].parent is None,
        forall|x: int| #![trigger adopt(doc, node).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& adopt(doc, node).nodes[x].kind == doc.nodes[x].kind
            &&& adopt(doc, node).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node ==> adopt(doc, node).nodes[x].parent == doc.nodes[x].parent)
        },
{
    if doc.nodes[node as int].parent is Some {
        theorem_remove_wf(doc, node);
        theorem_remove_keeps_record(doc, node);
    }
}

// ---------------------------------------------------------------------
// clone a node (shallow)

/// DOM §4.4† "clone a node" (shallow) keeps the arena well formed and adds
/// the copy (and a template's contents): the copy is the next id, has the
/// kind of [`clone_kind`] and no parent or children, a template's
/// contents is the id after it, and no existing node changes.
pub proof fn theorem_clone_node_wf(doc: Document, node: NodeId)
    requires
        clone_requires(doc, node),
        can_create(doc, clone_count(doc, node)),
    ensures
        wf(clone_node(doc, node).0),
        clone_node(doc, node).1 == doc.nodes.len(),
        clone_node(doc, node).0.nodes.len() == doc.nodes.len() + clone_count(doc, node),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] clone_node(doc, node).0.nodes[i] == doc.nodes[i],
        ({
            let (d, copy) = clone_node(doc, node);
            let k = doc.nodes[node as int].kind;
            &&& d.nodes[copy as int].parent is None
            &&& d.nodes[copy as int].children.len() == 0
            &&& d.nodes[copy as int].wrapper is None
            &&& is_template(k) ==> {
                &&& d.nodes[copy as int].kind is Element
                &&& d.nodes[copy as int].kind->Element_template_contents == Some((copy + 1) as NodeId)
                &&& d.nodes[copy as int].kind->Element_attributes == k->Element_attributes
                &&& d.nodes[copy as int].kind->Element_local_name == k->Element_local_name
                &&& d.nodes[copy as int].kind->Element_namespace == k->Element_namespace
                &&& d.nodes[copy as int].kind->Element_prefix == k->Element_prefix
                &&& d.nodes[copy as int].kind->Element_form_owner is None
                &&& d.nodes[(copy + 1) as int].kind == (NodeKind::DocumentFragment { host: Some(copy) })
            }
            &&& !is_template(k) ==> d.nodes[copy as int].kind == clone_kind(k)
            &&& k is Element ==> {
                &&& d.nodes[copy as int].kind is Element
                &&& d.nodes[copy as int].kind->Element_attributes == k->Element_attributes
                &&& d.nodes[copy as int].kind->Element_local_name == k->Element_local_name
                &&& d.nodes[copy as int].kind->Element_namespace == k->Element_namespace
                &&& d.nodes[copy as int].kind->Element_prefix == k->Element_prefix
                &&& d.nodes[copy as int].kind->Element_form_owner is None
            }
            &&& !(k is Element) && !(k is DocumentFragment) ==> d.nodes[copy as int].kind == k
            &&& k is DocumentFragment ==> d.nodes[copy as int].kind == (NodeKind::DocumentFragment { host: None })
        }),
{
    let k = doc.nodes[node as int].kind;
    let ck = clone_kind(k);
    assert(creatable(doc, ck));
    theorem_create_node_wf(doc, ck);
    let (d1, copy) = create_node(doc, ck);
    if is_template(k) {
        assert(d1.nodes[copy as int].kind is Element);
        assert(d1.nodes[copy as int].kind->Element_template_contents is None);
        theorem_create_template_contents_wf(d1, copy);
        theorem_create_template_contents_frame(d1, copy);
    }
}


// ---------------------------------------------------------------------
// Helpers: ancestors, next sibling

/// An inclusive ancestor is a host-including inclusive ancestor, with the
/// same fuel.
pub proof fn lemma_incl_implies_host(doc: Document, a: NodeId, x: NodeId, fuel: nat)
    ensures
        inclusive_ancestor_within(doc, a, x, fuel) ==> host_including_within(doc, a, x, fuel),
    decreases fuel,
{
    if x != a && fuel > 0 {
        if let Some(p) = parent(doc, x) {
            lemma_incl_implies_host(doc, a, p, (fuel - 1) as nat);
        }
    }
}

/// A node that is not a host-including inclusive ancestor of `x` is not an
/// inclusive ancestor of it.
pub proof fn lemma_not_host_not_incl(doc: Document, a: NodeId, x: NodeId)
    requires
        !is_host_including_inclusive_ancestor(doc, a, x),
    ensures
        !is_inclusive_ancestor(doc, a, x),
{
    lemma_incl_implies_host(doc, a, x, doc.nodes.len());
}

/// What "next sibling" is, for a node with a parent in a well-formed
/// arena: the entry after it in its parent's children, which is a child of
/// the same parent, another node, and at the next index.
pub proof fn lemma_next_sibling(doc: Document, n: NodeId)
    requires
        wf(doc),
        valid(doc, n),
        parent(doc, n) is Some,
    ensures
        ({
            let p = parent(doc, n)->Some_0;
            let kids = children(doc, p);
            let i = index_of(kids, n);
            &&& valid(doc, p)
            &&& 0 <= i < kids.len()
            &&& kids[i] == n
            &&& match next_sibling(doc, n) {
                Some(x) => {
                    &&& i + 1 < kids.len()
                    &&& x == kids[i + 1]
                    &&& valid(doc, x)
                    &&& parent(doc, x) == Some(p)
                    &&& x != n
                    &&& index_of(kids, x) == i + 1
                },
                None => i + 1 == kids.len(),
            }
        }),
{
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
    let p = parent(doc, n)->Some_0;
    let kids = children(doc, p);
    assert(kids.contains(n));
    lemma_index_of(kids, n);
    let i = index_of(kids, n);
    assert(kids.no_duplicates());
    if i + 1 < kids.len() {
        lemma_index_of_unique(kids, i + 1);
        let x = kids[i + 1];
        assert(doc.nodes[p as int].children[i + 1] == x);
        assert(x != n);
    }
}

proof fn lemma_remove_paths_contains(paths: Seq<Seq<NodeId>>, node: NodeId, x: int, a: NodeId)
    requires
        0 <= x < paths.len(),
        node < paths.len(),
        paths[node as int].len() >= 1,
        paths[x].contains(node) ==> paths[node as int].len() <= paths[x].len(),
    ensures
        remove_paths(paths, node)[x].contains(a) ==> paths[x].contains(a),
{
    let q = remove_paths(paths, node);
    if q[x].contains(a) {
        if paths[x].contains(node) {
            let m = paths[node as int].len() - 1;
            let s = paths[x].subrange(m, paths[x].len() as int);
            assert(q[x] == s);
            let k = choose|k: int| 0 <= k < s.len() && #[trigger] s[k] == a;
            assert(0 <= m);
            assert(s[k] == paths[x][m + k]);
            assert(paths[x][m + k] == a);
            assert(paths[x].contains(a));
        } else {
            assert(q[x] == paths[x]);
        }
    }
}

/// Removing a node never makes something an ancestor that was not: an
/// inclusive ancestor in the arena after is one before.
pub proof fn lemma_remove_ancestor_mono(doc: Document, node: NodeId, a: NodeId, x: NodeId)
    requires
        super::contract::remove_requires(doc, node),
        valid(doc, x),
    ensures
        is_inclusive_ancestor(remove(doc, node), a, x) ==> is_inclusive_ancestor(doc, a, x),
{
    let paths = lemma_wf_witness(doc);
    lemma_remove_wf_with(doc, paths, node);
    lemma_remove_nodes(doc, paths, node);
    let d = remove(doc, node);
    let q = remove_paths(paths, node);
    assert(valid(d, x));
    lemma_ancestor_iff_path(doc, paths, a, x);
    lemma_ancestor_iff_path(d, q, a, x);
    lemma_path(doc, paths, node);
    if paths[x as int].contains(node) {
        lemma_path_prefix(doc, paths, node, x);
    }
    lemma_remove_paths_contains(paths, node, x as int, a);
}

// ---------------------------------------------------------------------
// Removing all of a node's children

/// The records after the first `k` children of `p` have been removed: `p`
/// has lost them from its children and each has no parent.
pub open spec fn removed_prefix(d: Document, p: NodeId, k: int) -> Seq<Node> {
    let kids = d.nodes[p as int].children;
    Seq::new(
        d.nodes.len(),
        |x: int|
            if x == p {
                Node { children: kids.subrange(k, kids.len() as int), ..d.nodes[x] }
            } else if kids.subrange(0, k).contains(x as NodeId) {
                Node { parent: None, ..d.nodes[x] }
            } else {
                d.nodes[x]
            },
    )
}

/// Dropping the first element moves the prefix by one.
proof fn lemma_contains_shift(kids: Seq<NodeId>, k: int, x: NodeId)
    requires
        1 <= k <= kids.len(),
    ensures
        kids.subrange(0, k).contains(kids[0]),
        x != kids[0] ==> (kids.subrange(0, k).contains(x) <==> kids.remove(0).subrange(0, k - 1).contains(x)),
{
    let a = kids.subrange(0, k);
    let b = kids.remove(0).subrange(0, k - 1);
    assert(a[0] == kids[0]);
    if x != kids[0] {
        if a.contains(x) {
            let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
            assert(j >= 1);
            assert(b[j - 1] == x);
        }
        if b.contains(x) {
            let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
            assert(a[j + 1] == x);
        }
    }
}

/// Removing the first child of `p` and then `k - 1` more is removing `k`:
/// the records after the one removal and `k - 1` more prefix are
/// [`removed_prefix`] with `k`.
#[verifier::rlimit(50)]
proof fn lemma_removed_prefix_step(d: Document, p: NodeId, k: int)
    requires
        wf(d),
        valid(d, p),
        1 <= k <= d.nodes[p as int].children.len(),
    ensures
        ({
            let c0 = d.nodes[p as int].children[0];
            &&& super::contract::remove_requires(d, c0)
            &&& wf(remove(d, c0))
            &&& valid(remove(d, c0), p)
            &&& children(remove(d, c0), p).len() + 1 == d.nodes[p as int].children.len()
            &&& removed_prefix(remove(d, c0), p, k - 1) == removed_prefix(d, p, k)
        }),
{
    let kids = d.nodes[p as int].children;
    let n = d.nodes.len();
    let paths = lemma_wf_witness(d);
    lemma_wf_split(d, paths);
    let c0 = kids[0];
    assert(d.nodes[p as int].children[0] == c0);
    assert(c0 < n);
    assert(d.nodes[c0 as int].parent == Some(p));
    assert(super::contract::remove_requires(d, c0));
    let d1 = remove(d, c0);
    theorem_remove_wf(d, c0);
    theorem_remove_keeps_order(d, c0);
    theorem_remove_keeps_record(d, c0);
    assert(kids.no_duplicates());
    lemma_index_of_unique(kids, 0);
    let kids1 = kids.remove(0);
    assert(children(d1, p) == kids1);
    assert(kids1 =~= kids.subrange(1, kids.len() as int));
    lemma_seq_remove(kids, 0);
    let r = removed_prefix(d, p, k);
    let r1 = removed_prefix(d1, p, k - 1);
    assert(c0 != p);
    assert(d1.nodes.len() == n);
    assert forall|x: int| 0 <= x < n implies #[trigger] r1[x] == r[x] by {
        let xn = x as NodeId;
        if x == p {
            assert(kids1.subrange(k - 1, kids1.len() as int) =~= kids.subrange(k, kids.len() as int));
            assert(d1.nodes[x].kind == d.nodes[x].kind);
            assert(d1.nodes[x].parent == d.nodes[x].parent);
            assert(d1.nodes[x].wrapper == d.nodes[x].wrapper);
        } else {
            lemma_contains_shift(kids, k, xn);
            if x == c0 {
                assert(!kids1.contains(c0));
                assert(!kids1.subrange(0, k - 1).contains(c0)) by {
                    if kids1.subrange(0, k - 1).contains(c0) {
                        let j = choose|j: int| 0 <= j < k - 1 && #[trigger] kids1.subrange(0, k - 1)[j] == c0;
                        assert(kids1[j] == c0);
                    }
                }
                assert(d1.nodes[x].kind == d.nodes[x].kind);
                assert(d1.nodes[x].children == d.nodes[x].children);
                assert(d1.nodes[x].wrapper == d.nodes[x].wrapper);
            } else {
                assert(d1.nodes[x] == d.nodes[x]);
            }
        }
    }
    assert(r1 =~= r);
}

/// Nothing removed is the arena itself.
proof fn lemma_removed_prefix_zero(d: Document, p: NodeId)
    requires
        valid(d, p),
    ensures
        removed_prefix(d, p, 0) == d.nodes,
{
    let kids = d.nodes[p as int].children;
    let r = removed_prefix(d, p, 0);
    assert(kids.subrange(0, kids.len() as int) =~= kids);
    assert forall|x: int| 0 <= x < d.nodes.len() implies #[trigger] r[x] == d.nodes[x] by {
        if x != p {
            assert(!kids.subrange(0, 0).contains(x as NodeId));
        }
    }
    assert(r =~= d.nodes);
}

/// Removing the first `k` children of `p` one by one keeps the arena well
/// formed and gives [`removed_prefix`].
pub proof fn lemma_remove_children_n(d: Document, p: NodeId, k: nat)
    requires
        wf(d),
        valid(d, p),
        k <= d.nodes[p as int].children.len(),
    ensures
        wf(remove_children_n(d, p, k)),
        remove_children_n(d, p, k).nodes == removed_prefix(d, p, k as int),
    decreases k,
{
    let kids = d.nodes[p as int].children;
    if k == 0 {
        lemma_removed_prefix_zero(d, p);
    } else {
        lemma_removed_prefix_step(d, p, k as int);
        let c0 = kids[0];
        let d1 = remove(d, c0);
        assert(remove_children_n(d, p, k) == remove_children_n(d1, p, (k - 1) as nat));
        lemma_remove_children_n(d1, p, (k - 1) as nat);
        assert((k - 1) as nat as int == k as int - 1);
    }
}

/// Removing the first `k` children of `p` never makes a node an ancestor
/// that was not.
pub proof fn lemma_remove_children_n_ancestors(d: Document, p: NodeId, k: nat, a: NodeId, x: NodeId)
    requires
        wf(d),
        valid(d, p),
        k <= d.nodes[p as int].children.len(),
        valid(d, x),
    ensures
        is_inclusive_ancestor(remove_children_n(d, p, k), a, x) ==> is_inclusive_ancestor(d, a, x),
    decreases k,
{
    let kids = d.nodes[p as int].children;
    if k > 0 {
        lemma_removed_prefix_step(d, p, k as int);
        let c0 = kids[0];
        let d1 = remove(d, c0);
        assert(remove_children_n(d, p, k) == remove_children_n(d1, p, (k - 1) as nat));
        lemma_remove_children_n_ancestors(d1, p, (k - 1) as nat, a, x);
        lemma_remove_ancestor_mono(d, c0, a, x);
    }
}

// ---------------------------------------------------------------------
// Inserting a list of nodes

/// What `parent`'s children `kids` become when `nodes` are inserted before
/// `child`, in order, each before it: the list goes where `child` was.
pub open spec fn list_kids(kids: Seq<NodeId>, nodes: Seq<NodeId>, child: Option<NodeId>) -> Seq<NodeId> {
    match child {
        None => kids + nodes,
        Some(c) => {
            let i = index_of(kids, c);
            kids.subrange(0, i) + nodes + kids.subrange(i, kids.len() as int)
        },
    }
}

/// The records after [`insert_list`]: `parent`'s children are
/// [`list_kids`], each inserted node has `parent` as its parent.
pub open spec fn list_inserted(d: Document, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>) -> Seq<Node> {
    Seq::new(
        d.nodes.len(),
        |x: int|
            if x == parent {
                Node { children: list_kids(d.nodes[parent as int].children, nodes, child), ..d.nodes[x] }
            } else if nodes.contains(x as NodeId) {
                Node { parent: Some(parent), ..d.nodes[x] }
            } else {
                d.nodes[x]
            },
    )
}

/// Inserting `n0` and then the rest is inserting the list.
proof fn lemma_list_kids_step(kids: Seq<NodeId>, n0: NodeId, rest: Seq<NodeId>, child: Option<NodeId>)
    requires
        kids.no_duplicates(),
        !kids.contains(n0),
        child is Some ==> kids.contains(child->Some_0),
    ensures
        list_kids(insert_into(kids, n0, child), rest, child) == list_kids(kids, seq![n0] + rest, child),
{
    match child {
        None => {
            assert(kids.push(n0) + rest =~= kids + (seq![n0] + rest));
        },
        Some(c) => {
            lemma_index_of(kids, c);
            let i = index_of(kids, c);
            lemma_seq_insert(kids, i, n0);
            let kids1 = kids.insert(i, n0);
            assert(kids1[i + 1] == kids[i]);
            assert(kids1[i + 1] == c);
            lemma_index_of_unique(kids1, i + 1);
            assert(index_of(kids1, c) == i + 1);
            assert(kids1.subrange(0, i + 1) =~= kids.subrange(0, i).push(n0));
            assert(kids1.subrange(i + 1, kids1.len() as int) =~= kids.subrange(i, kids.len() as int));
            assert(kids.subrange(0, i).push(n0) + rest + kids.subrange(i, kids.len() as int) =~= kids.subrange(0, i) + (seq![n0] + rest)
                + kids.subrange(i, kids.len() as int));
        },
    }
}

/// What [`insert_list`] asks of its arguments.
pub open spec fn insert_list_requires(
    d: Document,
    paths: Seq<Seq<NodeId>>,
    nodes: Seq<NodeId>,
    parent: NodeId,
    child: Option<NodeId>,
) -> bool {
    &&& wf_with(d, paths)
    &&& valid(d, parent)
    &&& may_have_children(d.nodes[parent as int].kind)
    &&& nodes.no_duplicates()
    &&& forall|j: int| 0 <= j < nodes.len() ==> {
        &&& (#[trigger] nodes[j]) < d.nodes.len()
        &&& d.nodes[nodes[j] as int].parent is None
        &&& !(d.nodes[nodes[j] as int].kind is Document)
        &&& !(d.nodes[nodes[j] as int].kind is DocumentFragment)
        &&& !paths[parent as int].contains(nodes[j])
    }
    &&& match child {
        None => true,
        Some(c) => valid(d, c) && d.nodes[c as int].parent == Some(parent),
    }
}

/// The first step of [`insert_list`] is a valid "insert" that keeps the
/// requirements of the rest.
proof fn lemma_insert_list_step_requires(d: Document, paths: Seq<Seq<NodeId>>, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>)
    requires
        insert_list_requires(d, paths, nodes, parent, child),
        nodes.len() > 0,
    ensures
        ({
            let n0 = nodes[0];
            let rest = nodes.drop_first();
            let d1 = insert(d, n0, parent, child);
            let q = insert_paths(d, paths, n0, parent);
            &&& insert_requires(d, n0, parent, child)
            &&& wf_with(d1, q)
            &&& d1.nodes.len() == d.nodes.len()
            &&& insert_list_requires(d1, q, rest, parent, child)
        }),
{
    let n = d.nodes.len();
    lemma_wf_split(d, paths);
    lemma_path(d, paths, parent);
    let n0 = nodes[0];
    let rest = nodes.drop_first();
    assert(nodes[0] < n);
    assert(!paths[parent as int].contains(n0));
    assert(n0 != parent);
    lemma_ancestor_iff_path(d, paths, n0, parent);
    assert(insert_requires(d, n0, parent, child)) by {
        if let Some(c) = child {
            assert(d.nodes[c as int].parent is Some);
            assert(c != n0);
        }
    }
    let d1 = insert(d, n0, parent, child);
    lemma_insert_is_attach(d, n0, parent, child);
    assert(adopt(d, n0) == d);
    lemma_insert_attach_requires(d, paths, n0, parent, child);
    let kids = d.nodes[parent as int].children;
    let kids1 = insert_kids(d, n0, parent, child);
    lemma_attach_nodes(d, paths, n0, parent, kids1);
    lemma_insert_wf_with(d, paths, n0, parent, child);
    let q = insert_paths(d, paths, n0, parent);
    assert(q[parent as int] == paths[parent as int]);
    assert(d1.nodes.len() == n);
    assert forall|j: int| 0 <= j < rest.len() implies {
        &&& (#[trigger] rest[j]) < d1.nodes.len()
        &&& d1.nodes[rest[j] as int].parent is None
        &&& !(d1.nodes[rest[j] as int].kind is Document)
        &&& !(d1.nodes[rest[j] as int].kind is DocumentFragment)
        &&& !q[parent as int].contains(rest[j])
    } by {
        assert(rest[j] == nodes[j + 1]);
        assert(rest[j] != n0);
        assert(rest[j] != parent);
    }
    assert(rest.no_duplicates());
    if let Some(c) = child {
        assert(c != n0);
        lemma_parent_not_self(d, paths, c);
        assert(c != parent);
    }
}

/// Dropping the first element keeps the others.
proof fn lemma_drop_first_contains(nodes: Seq<NodeId>, x: NodeId)
    requires
        nodes.len() > 0,
        x != nodes[0],
    ensures
        nodes.contains(x) <==> nodes.drop_first().contains(x),
{
    if nodes.contains(x) {
        let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == x;
        assert(j != 0);
        assert(nodes.drop_first()[j - 1] == nodes[j]);
    }
    if nodes.drop_first().contains(x) {
        let j = choose|j: int| 0 <= j < nodes.drop_first().len() && nodes.drop_first()[j] == x;
        assert(nodes[j + 1] == x);
    }
}

/// What the first step of [`insert_list`] does to the records: `parent`
/// gets `n0` among its children, `n0` gets `parent` as its parent, and
/// nothing else changes.
proof fn lemma_insert_list_step_nodes(d: Document, paths: Seq<Seq<NodeId>>, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>)
    requires
        insert_list_requires(d, paths, nodes, parent, child),
        nodes.len() > 0,
    ensures
        ({
            let n0 = nodes[0];
            let d1 = insert(d, n0, parent, child);
            let kids = d.nodes[parent as int].children;
            &&& n0 != parent
            &&& d1.nodes.len() == d.nodes.len()
            &&& !kids.contains(n0)
            &&& d1.nodes[parent as int] == (Node { children: insert_into(kids, n0, child), ..d.nodes[parent as int] })
            &&& d1.nodes[n0 as int] == (Node { parent: Some(parent), ..d.nodes[n0 as int] })
            &&& forall|x: int| 0 <= x < d.nodes.len() && x != parent && x != n0 ==> #[trigger] d1.nodes[x] == d.nodes[x]
        }),
{
    lemma_wf_split(d, paths);
    lemma_path(d, paths, parent);
    let n0 = nodes[0];
    assert(nodes[0] < d.nodes.len());
    assert(!paths[parent as int].contains(n0));
    assert(n0 != parent);
    lemma_ancestor_iff_path(d, paths, n0, parent);
    assert(insert_requires(d, n0, parent, child)) by {
        if let Some(c) = child {
            assert(d.nodes[c as int].parent is Some);
            assert(c != n0);
        }
    }
    lemma_insert_is_attach(d, n0, parent, child);
    assert(adopt(d, n0) == d);
    lemma_insert_attach_requires(d, paths, n0, parent, child);
    let kids1 = insert_kids(d, n0, parent, child);
    lemma_attach_nodes(d, paths, n0, parent, kids1);
    assert(kids1 == insert_into(d.nodes[parent as int].children, n0, child));
}

/// The records after the first step of [`insert_list`] and then the rest
/// are those of the whole list.
#[verifier::rlimit(50)]
proof fn lemma_insert_list_step_records(d: Document, paths: Seq<Seq<NodeId>>, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>)
    requires
        insert_list_requires(d, paths, nodes, parent, child),
        nodes.len() > 0,
    ensures
        list_inserted(insert(d, nodes[0], parent, child), nodes.drop_first(), parent, child) == list_inserted(d, nodes, parent, child),
{
    let n = d.nodes.len();
    lemma_wf_split(d, paths);
    let n0 = nodes[0];
    let rest = nodes.drop_first();
    let kids = d.nodes[parent as int].children;
    lemma_insert_list_step_nodes(d, paths, nodes, parent, child);
    let d1 = insert(d, n0, parent, child);
    lemma_listed(d, paths, n0, parent, child);
    if let Some(c) = child {
        assert(d.nodes[c as int].parent == Some(parent));
        assert(kids.contains(c));
    }
    lemma_list_kids_step(kids, n0, rest, child);
    assert(seq![n0] + rest =~= nodes);
    assert(nodes.no_duplicates());
    assert(!rest.contains(n0)) by {
        if rest.contains(n0) {
            let j = choose|j: int| 0 <= j < rest.len() && rest[j] == n0;
            assert(nodes[j + 1] == n0);
        }
    }
    assert(nodes.contains(n0));
    let a = list_inserted(d1, rest, parent, child);
    let b = list_inserted(d, nodes, parent, child);
    assert forall|x: int| 0 <= x < n implies #[trigger] a[x] == b[x] by {
        if x != parent && x != n0 {
            lemma_drop_first_contains(nodes, x as NodeId);
        }
    }
    assert(a =~= b);
}

/// No nodes inserted is the arena itself.
proof fn lemma_list_inserted_empty(d: Document, parent: NodeId, child: Option<NodeId>)
    requires
        wf(d),
        valid(d, parent),
        match child {
            None => true,
            Some(c) => valid(d, c) && d.nodes[c as int].parent == Some(parent),
        },
    ensures
        list_inserted(d, seq![], parent, child) == d.nodes,
{
    let paths = lemma_wf_witness(d);
    lemma_wf_split(d, paths);
    let nodes = Seq::<NodeId>::empty();
    let kids = d.nodes[parent as int].children;
    if let Some(c) = child {
        assert(kids.contains(c));
        lemma_index_of(kids, c);
        let i = index_of(kids, c);
        assert(kids.subrange(0, i) + nodes + kids.subrange(i, kids.len() as int) =~= kids);
    } else {
        assert(kids + nodes =~= kids);
    }
    assert(list_kids(kids, nodes, child) =~= kids);
    let r = list_inserted(d, nodes, parent, child);
    assert forall|x: int| 0 <= x < d.nodes.len() implies #[trigger] r[x] == d.nodes[x] by {
        if x != parent {
            assert(!nodes.contains(x as NodeId));
        }
    }
    assert(r =~= d.nodes);
}

/// Inserting parentless nodes, one after the other, before `child`, keeps
/// the arena well formed and gives [`list_inserted`].
pub proof fn lemma_insert_list(d: Document, paths: Seq<Seq<NodeId>>, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>)
    requires
        insert_list_requires(d, paths, nodes, parent, child),
    ensures
        wf(insert_list(d, nodes, parent, child)),
        insert_list(d, nodes, parent, child).nodes == list_inserted(d, nodes, parent, child),
    decreases nodes.len(),
{
    if nodes.len() == 0 {
        assert(nodes =~= seq![]);
        lemma_list_inserted_empty(d, parent, child);
    } else {
        lemma_insert_list_step_requires(d, paths, nodes, parent, child);
        lemma_insert_list_step_records(d, paths, nodes, parent, child);
        let d1 = insert(d, nodes[0], parent, child);
        let q = insert_paths(d, paths, nodes[0], parent);
        lemma_insert_list(d1, q, nodes.drop_first(), parent, child);
    }
}

// ---------------------------------------------------------------------
// insert, for any node

/// What [`insert_any`] asks of its arguments: [`insert_requires`] without
/// the restriction to non-fragments (a fragment must not be an inclusive
/// ancestor of `parent`, which excludes `parent` itself).
pub open spec fn insert_any_requires(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& wf(doc)
    &&& valid(doc, node)
    &&& valid(doc, parent)
    &&& !(doc.nodes[node as int].kind is Document)
    &&& may_have_children(doc.nodes[parent as int].kind)
    &&& !is_inclusive_ancestor(doc, node, parent)
    &&& match child {
        None => true,
        Some(c) => valid(doc, c) && c != node && doc.nodes[c as int].parent == Some(parent),
    }
}

/// The records after inserting the fragment `frag`: its children have
/// moved, in order, to `parent`'s children (before `child`, or at the
/// end) and have `parent` as their parent; `frag` has no children.
pub open spec fn fragment_inserted(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>) -> Seq<Node> {
    let nodes = d.nodes[frag as int].children;
    Seq::new(
        d.nodes.len(),
        |x: int|
            if x == frag {
                Node { children: seq![], ..d.nodes[x] }
            } else if x == parent {
                Node { children: list_kids(d.nodes[parent as int].children, nodes, child), ..d.nodes[x] }
            } else if nodes.contains(x as NodeId) {
                Node { parent: Some(parent), ..d.nodes[x] }
            } else {
                d.nodes[x]
            },
    )
}

/// A child of `frag` is not an inclusive ancestor of `parent` if `frag`
/// is not.
proof fn lemma_frag_child_not_ancestor(d: Document, paths: Seq<Seq<NodeId>>, frag: NodeId, parent: NodeId, c: NodeId)
    requires
        wf_with(d, paths),
        valid(d, frag),
        valid(d, parent),
        valid(d, c),
        d.nodes[c as int].parent == Some(frag),
        !is_inclusive_ancestor(d, frag, parent),
    ensures
        !is_inclusive_ancestor(d, c, parent),
{
    lemma_ancestor_iff_path(d, paths, c, parent);
    lemma_ancestor_iff_path(d, paths, frag, parent);
    if paths[parent as int].contains(c) {
        lemma_path_prefix(d, paths, c, parent);
        lemma_path(d, paths, frag);
        assert(paths[c as int] == paths[frag as int].push(c));
        let m = paths[frag as int].len() - 1;
        assert(paths[c as int][m] == paths[frag as int][m]);
        assert(paths[c as int].contains(frag));
    }
}

/// What [`insert_any_requires`] gives about the children of a fragment
/// being inserted.
pub proof fn lemma_frag_facts(d: Document, paths: Seq<Seq<NodeId>>, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(d, frag, parent, child),
        wf_with(d, paths),
        d.nodes[frag as int].kind is DocumentFragment,
    ensures
        ({
            let nodes = d.nodes[frag as int].children;
            let kids = d.nodes[parent as int].children;
            &&& parent != frag
            &&& nodes.no_duplicates()
            &&& forall|j: int| 0 <= j < nodes.len() ==> {
                &&& (#[trigger] nodes[j]) < d.nodes.len()
                &&& d.nodes[nodes[j] as int].parent == Some(frag)
                &&& nodes[j] != frag
                &&& !is_inclusive_ancestor(d, nodes[j], parent)
                &&& nodes[j] != parent
                &&& !(d.nodes[nodes[j] as int].kind is Document)
                &&& !(d.nodes[nodes[j] as int].kind is DocumentFragment)
            }
            &&& !nodes.contains(parent)
            &&& !nodes.contains(frag)
            &&& match child {
                None => true,
                Some(c) => !nodes.contains(c) && c != frag && kids.contains(c),
            }
        }),
{
    let n = d.nodes.len();
    lemma_wf_split(d, paths);
    let nodes = d.nodes[frag as int].children;
    let kids = d.nodes[parent as int].children;
    assert(parent != frag);
    assert(nodes.no_duplicates());
    assert forall|j: int| 0 <= j < nodes.len() implies {
        &&& (#[trigger] nodes[j]) < n
        &&& d.nodes[nodes[j] as int].parent == Some(frag)
        &&& nodes[j] != frag
        &&& !is_inclusive_ancestor(d, nodes[j], parent)
        &&& nodes[j] != parent
        &&& !(d.nodes[nodes[j] as int].kind is Document)
        &&& !(d.nodes[nodes[j] as int].kind is DocumentFragment)
    } by {
        let c = nodes[j];
        assert(d.nodes[frag as int].children[j] == c);
        lemma_parent_not_self(d, paths, c);
        lemma_frag_child_not_ancestor(d, paths, frag, parent, c);
        assert(d.nodes[c as int].parent is Some);
        assert(c != 0);
    }
    if let Some(c) = child {
        assert(d.nodes[c as int].parent == Some(parent));
        assert(!nodes.contains(c)) by {
            if nodes.contains(c) {
                let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == c;
                assert(d.nodes[nodes[j] as int].parent == Some(frag));
            }
        }
        assert(kids.contains(c));
    }
    assert(!nodes.contains(parent)) by {
        if nodes.contains(parent) {
            let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == parent;
            assert(nodes[j] != parent);
        }
    }
    assert(!nodes.contains(frag)) by {
        if nodes.contains(frag) {
            let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == frag;
            assert(nodes[j] != frag);
        }
    }
}

/// An empty fragment inserts nothing.
#[verifier::rlimit(50)]
proof fn lemma_insert_fragment_empty(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(d, frag, parent, child),
        d.nodes[frag as int].kind is DocumentFragment,
        d.nodes[frag as int].children.len() == 0,
    ensures
        wf(insert_fragment(d, frag, parent, child)),
        insert_fragment(d, frag, parent, child).nodes == fragment_inserted(d, frag, parent, child),
{
    let n = d.nodes.len();
    let paths = lemma_wf_witness(d);
    lemma_frag_facts(d, paths, frag, parent, child);
    let nodes = d.nodes[frag as int].children;
    let kids = d.nodes[parent as int].children;
    assert(nodes =~= seq![]);
    let r = fragment_inserted(d, frag, parent, child);
    if let Some(c) = child {
        lemma_index_of(kids, c);
    }
    assert(list_kids(kids, nodes, child) =~= kids) by {
        if let Some(c) = child {
            let i = index_of(kids, c);
            assert(kids.subrange(0, i) + nodes + kids.subrange(i, kids.len() as int) =~= kids);
        } else {
            assert(kids + nodes =~= kids);
        }
    }
    assert forall|x: int| 0 <= x < n implies #[trigger] r[x] == d.nodes[x] by {
        if x == frag {
            assert(d.nodes[x].children =~= seq![]);
        } else if x != parent {
            assert(!nodes.contains(x as NodeId));
        }
    }
    assert(r =~= d.nodes);
}

/// A fragment with children: the arena after step 4.1.
proof fn lemma_insert_fragment_removed(d: Document, paths: Seq<Seq<NodeId>>, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(d, frag, parent, child),
        wf_with(d, paths),
        d.nodes[frag as int].kind is DocumentFragment,
        d.nodes[frag as int].children.len() > 0,
    ensures
        ({
            let nodes = d.nodes[frag as int].children;
            let d1 = remove_children(d, frag);
            &&& wf(d1)
            &&& d1.nodes == removed_prefix(d, frag, nodes.len() as int)
            &&& d1.nodes.len() == d.nodes.len()
            &&& d1.nodes[parent as int] == d.nodes[parent as int]
        }),
{
    let n = d.nodes.len();
    lemma_frag_facts(d, paths, frag, parent, child);
    let nodes = d.nodes[frag as int].children;
    let len = nodes.len();
    lemma_remove_children_n(d, frag, len);
    let d1 = remove_children(d, frag);
    assert(children(d, frag) == nodes);
    assert(d1.nodes == removed_prefix(d, frag, len as int));
    assert(nodes.subrange(0, len as int) =~= nodes);
    assert(d1.nodes.len() == n);
    assert(d1.nodes[parent as int] == d.nodes[parent as int]);
}

/// The arena after step 4.1 meets what [`insert_list`] asks.
proof fn lemma_insert_fragment_requires(
    d: Document,
    paths: Seq<Seq<NodeId>>,
    paths1: Seq<Seq<NodeId>>,
    frag: NodeId,
    parent: NodeId,
    child: Option<NodeId>,
)
    requires
        insert_any_requires(d, frag, parent, child),
        wf_with(d, paths),
        d.nodes[frag as int].kind is DocumentFragment,
        d.nodes[frag as int].children.len() > 0,
        wf_with(remove_children(d, frag), paths1),
    ensures
        insert_list_requires(remove_children(d, frag), paths1, d.nodes[frag as int].children, parent, child),
{
    let nodes = d.nodes[frag as int].children;
    let len = nodes.len();
    lemma_frag_facts(d, paths, frag, parent, child);
    lemma_insert_fragment_removed(d, paths, frag, parent, child);
    let d1 = remove_children(d, frag);
    assert forall|j: int| 0 <= j < nodes.len() implies {
        &&& (#[trigger] nodes[j]) < d1.nodes.len()
        &&& d1.nodes[nodes[j] as int].parent is None
        &&& !(d1.nodes[nodes[j] as int].kind is Document)
        &&& !(d1.nodes[nodes[j] as int].kind is DocumentFragment)
        &&& !paths1[parent as int].contains(nodes[j])
    } by {
        let c = nodes[j];
        assert(nodes.subrange(0, len as int)[j] == c);
        assert(nodes.subrange(0, len as int).contains(c));
        lemma_remove_children_n_ancestors(d, frag, len, c, parent);
        lemma_ancestor_iff_path(d1, paths1, c, parent);
    }
    if let Some(c) = child {
        assert(!nodes.subrange(0, len as int).contains(c));
        assert(d1.nodes[c as int] == d.nodes[c as int]);
    }
}

/// The records after step 4.1 and the list of step 7 are
/// [`fragment_inserted`].
proof fn lemma_fragment_records(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        valid(d, frag),
        valid(d, parent),
        parent != frag,
        d.nodes[frag as int].children.len() > 0,
        !d.nodes[frag as int].children.contains(frag),
        !d.nodes[frag as int].children.contains(parent),
        d.nodes[parent as int] == removed_prefix(d, frag, d.nodes[frag as int].children.len() as int)[parent as int],
    ensures
        list_inserted(
            Document { nodes: removed_prefix(d, frag, d.nodes[frag as int].children.len() as int) },
            d.nodes[frag as int].children,
            parent,
            child,
        ) == fragment_inserted(d, frag, parent, child),
{
    let n = d.nodes.len();
    let nodes = d.nodes[frag as int].children;
    let len = nodes.len();
    let d1 = Document { nodes: removed_prefix(d, frag, len as int) };
    let a = list_inserted(d1, nodes, parent, child);
    let b = fragment_inserted(d, frag, parent, child);
    assert(nodes.subrange(0, len as int) =~= nodes);
    assert(nodes.subrange(len as int, len as int) =~= seq![]);
    assert forall|x: int| 0 <= x < n implies #[trigger] a[x] == b[x] by {
        if x == frag {
        } else if x == parent {
        } else if nodes.contains(x as NodeId) {
        } else {
        }
    }
    assert(a =~= b);
}

/// Inserting a fragment keeps the arena well formed and gives
/// [`fragment_inserted`].
pub proof fn lemma_insert_fragment(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(d, frag, parent, child),
        d.nodes[frag as int].kind is DocumentFragment,
    ensures
        wf(insert_fragment(d, frag, parent, child)),
        insert_fragment(d, frag, parent, child).nodes == fragment_inserted(d, frag, parent, child),
{
    let nodes = d.nodes[frag as int].children;
    if nodes.len() == 0 {
        lemma_insert_fragment_empty(d, frag, parent, child);
    } else {
        let paths = lemma_wf_witness(d);
        lemma_insert_fragment_removed(d, paths, frag, parent, child);
        lemma_frag_facts(d, paths, frag, parent, child);
        let d1 = remove_children(d, frag);
        let paths1 = lemma_wf_witness(d1);
        lemma_insert_fragment_requires(d, paths, paths1, frag, parent, child);
        lemma_insert_list(d1, paths1, nodes, parent, child);
        assert(insert_list(d1, nodes, parent, child).nodes == list_inserted(d1, nodes, parent, child));
        lemma_fragment_records(d, frag, parent, child);
        assert(d1 == Document { nodes: removed_prefix(d, frag, nodes.len() as int) });
    }
}

/// What [`fragment_inserted`] keeps of each record.
proof fn lemma_fragment_frame(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        valid(d, frag),
        valid(d, parent),
        parent != frag,
        d.nodes.len() <= max_nodes(),
    ensures
        forall|x: int| 0 <= x < d.nodes.len() ==> {
            &&& (#[trigger] fragment_inserted(d, frag, parent, child)[x]).kind == d.nodes[x].kind
            &&& fragment_inserted(d, frag, parent, child)[x].wrapper == d.nodes[x].wrapper
            &&& (x != frag && !d.nodes[frag as int].children.contains(x as NodeId) ==> fragment_inserted(d, frag, parent, child)[x].parent == d.nodes[x].parent)
        },
{
    let f = fragment_inserted(d, frag, parent, child);
    assert forall|x: int| 0 <= x < d.nodes.len() implies {
        &&& (#[trigger] f[x]).kind == d.nodes[x].kind
        &&& f[x].wrapper == d.nodes[x].wrapper
        &&& (x != frag && !d.nodes[frag as int].children.contains(x as NodeId) ==> f[x].parent == d.nodes[x].parent)
    } by {
        if x == frag {
        } else if x == parent {
        } else if d.nodes[frag as int].children.contains(x as NodeId) {
        } else {
        }
    }
}

/// [`theorem_insert_any_wf`] for a fragment.
#[verifier::rlimit(100)]
proof fn lemma_insert_any_frag(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        doc.nodes[node as int].kind is DocumentFragment,
    ensures
        wf(insert_any(doc, node, parent, child)),
        insert_any(doc, node, parent, child).nodes.len() == doc.nodes.len(),
        forall|x: int| #![trigger insert_any(doc, node, parent, child).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& insert_any(doc, node, parent, child).nodes[x].kind == doc.nodes[x].kind
            &&& insert_any(doc, node, parent, child).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node && !(doc.nodes[node as int].kind is DocumentFragment && doc.nodes[node as int].children.contains(x as NodeId))
                ==> insert_any(doc, node, parent, child).nodes[x].parent == doc.nodes[x].parent)
        },
        insert_any(doc, node, parent, child).nodes[parent as int].children == list_kids(
            doc.nodes[parent as int].children,
            doc.nodes[node as int].children,
            child,
        ),
        insert_any(doc, node, parent, child).nodes[node as int].children.len() == 0,
        forall|j: int| 0 <= j < doc.nodes[node as int].children.len() ==>
            insert_any(doc, node, parent, child).nodes[#[trigger] doc.nodes[node as int].children[j] as int].parent == Some(parent),
{
    lemma_insert_fragment(doc, node, parent, child);
    let r = insert_fragment(doc, node, parent, child);
    let f = fragment_inserted(doc, node, parent, child);
    assert(r.nodes == f);
    lemma_fragment_inserted_parent(doc, node, parent, child);
    let nodes = doc.nodes[node as int].children;
    let paths = lemma_wf_witness(doc);
    lemma_frag_facts(doc, paths, node, parent, child);
    lemma_wf_split(doc, paths);
    lemma_fragment_frame(doc, node, parent, child);
    assert forall|j: int| 0 <= j < nodes.len() implies r.nodes[#[trigger] nodes[j] as int].parent == Some(parent) by {
        let c = nodes[j];
        assert(nodes.contains(c));
    }
}

/// [`theorem_insert_any_wf`] for a node that is not a fragment.
#[verifier::rlimit(100)]
proof fn lemma_insert_any_node(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        !(doc.nodes[node as int].kind is DocumentFragment),
    ensures
        wf(insert_any(doc, node, parent, child)),
        insert_any(doc, node, parent, child).nodes.len() == doc.nodes.len(),
        forall|x: int| #![trigger insert_any(doc, node, parent, child).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& insert_any(doc, node, parent, child).nodes[x].kind == doc.nodes[x].kind
            &&& insert_any(doc, node, parent, child).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node && !(doc.nodes[node as int].kind is DocumentFragment && doc.nodes[node as int].children.contains(x as NodeId))
                ==> insert_any(doc, node, parent, child).nodes[x].parent == doc.nodes[x].parent)
        },
        insert_any(doc, node, parent, child).nodes[node as int].parent == Some(parent),
        insert_any(doc, node, parent, child).nodes[parent as int].children == insert_kids(doc, node, parent, child),
{
    assert(insert_requires(doc, node, parent, child));
    theorem_insert_wf(doc, node, parent, child);
}

/// DOM §4.2.3 "insert", for any node, keeps the arena well formed and does
/// what its steps say: a node that is not a fragment is `parent`'s new
/// child (the parser's [`insert`]); a fragment is emptied, and each of its
/// children has `parent` as its parent. No kind or wrapper changes, and no
/// other node's parent does.
#[verifier::rlimit(100)]
pub proof fn theorem_insert_any_wf(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
    ensures
        wf(insert_any(doc, node, parent, child)),
        insert_any(doc, node, parent, child).nodes.len() == doc.nodes.len(),
        forall|x: int| #![trigger insert_any(doc, node, parent, child).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& insert_any(doc, node, parent, child).nodes[x].kind == doc.nodes[x].kind
            &&& insert_any(doc, node, parent, child).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node && !(doc.nodes[node as int].kind is DocumentFragment && doc.nodes[node as int].children.contains(x as NodeId))
                ==> insert_any(doc, node, parent, child).nodes[x].parent == doc.nodes[x].parent)
        },
        !(doc.nodes[node as int].kind is DocumentFragment) ==> insert_any(doc, node, parent, child).nodes[node as int].parent == Some(parent),
        !(doc.nodes[node as int].kind is DocumentFragment) ==> insert_any(doc, node, parent, child).nodes[parent as int].children == insert_kids(
            doc,
            node,
            parent,
            child,
        ),
        doc.nodes[node as int].kind is DocumentFragment ==> insert_any(doc, node, parent, child).nodes[parent as int].children == list_kids(
            doc.nodes[parent as int].children,
            doc.nodes[node as int].children,
            child,
        ),
        doc.nodes[node as int].kind is DocumentFragment ==> {
            &&& insert_any(doc, node, parent, child).nodes[node as int].children.len() == 0
            &&& forall|j: int| 0 <= j < doc.nodes[node as int].children.len() ==>
                insert_any(doc, node, parent, child).nodes[#[trigger] doc.nodes[node as int].children[j] as int].parent == Some(parent)
        },
{
    if doc.nodes[node as int].kind is DocumentFragment {
        lemma_insert_any_frag(doc, node, parent, child);
    } else {
        lemma_insert_any_node(doc, node, parent, child);
    }
}

/// The children of `parent` after inserting a fragment: the old ones with
/// the fragment's, in order, at the reference child.
pub proof fn lemma_insert_fragment_children(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        doc.nodes[node as int].kind is DocumentFragment,
    ensures
        insert_any(doc, node, parent, child).nodes[parent as int].children == list_kids(
            doc.nodes[parent as int].children,
            doc.nodes[node as int].children,
            child,
        ),
{
    lemma_insert_any_frag(doc, node, parent, child);
}

// ---------------------------------------------------------------------
// pre-insert

/// "referenceChild" after steps 2 and 3 of "pre-insert".
pub open spec fn pre_insert_reference(doc: Document, node: NodeId, child: Option<NodeId>) -> Option<NodeId> {
    if child == Some(node) {
        next_sibling(doc, node)
    } else {
        child
    }
}

/// A call without an error from "ensure pre-insertion validity" meets
/// what [`insert_any`] asks, with the reference child of step 3.
pub proof fn lemma_pre_insert_valid(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        pre_insert_error(doc, node, parent, child) is None,
    ensures
        insert_any_requires(doc, node, parent, pre_insert_reference(doc, node, child)),
        pre_insert(doc, node, parent, child) == insert_any(doc, node, parent, pre_insert_reference(doc, node, child)),
{
    lemma_not_host_not_incl(doc, node, parent);
    if child == Some(node) {
        assert(doc.nodes[node as int].parent == Some(parent));
        lemma_next_sibling(doc, node);
    }
}

/// DOM §4.2.3† "pre-insert" keeps the arena well formed. An error leaves
/// it as it is; without one it is "insert" ([`insert_any`]) at the
/// reference child, so the node (or a fragment's children) is a child of
/// `parent`. No kind or wrapper changes.
pub proof fn theorem_pre_insert_wf(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
    ensures
        wf(pre_insert(doc, node, parent, child)),
        pre_insert(doc, node, parent, child).nodes.len() == doc.nodes.len(),
        pre_insert_error(doc, node, parent, child) is Some ==> pre_insert(doc, node, parent, child) == doc,
        forall|x: int| #![trigger pre_insert(doc, node, parent, child).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& pre_insert(doc, node, parent, child).nodes[x].kind == doc.nodes[x].kind
            &&& pre_insert(doc, node, parent, child).nodes[x].wrapper == doc.nodes[x].wrapper
        },
        pre_insert_error(doc, node, parent, child) is None && !(doc.nodes[node as int].kind is DocumentFragment) ==>
            pre_insert(doc, node, parent, child).nodes[node as int].parent == Some(parent),
        pre_insert_error(doc, node, parent, child) is None && doc.nodes[node as int].kind is DocumentFragment ==> {
            &&& pre_insert(doc, node, parent, child).nodes[node as int].children.len() == 0
            &&& forall|j: int| 0 <= j < doc.nodes[node as int].children.len() ==>
                pre_insert(doc, node, parent, child).nodes[#[trigger] doc.nodes[node as int].children[j] as int].parent == Some(parent)
        },
{
    if pre_insert_error(doc, node, parent, child) is None {
        lemma_pre_insert_valid(doc, node, parent, child);
        let r = pre_insert_reference(doc, node, child);
        theorem_insert_any_wf(doc, node, parent, r);
    }
}


// ---------------------------------------------------------------------
// replace

/// "referenceChild" after steps 7 and 8 of "replace".
pub open spec fn replace_reference(doc: Document, child: NodeId, node: NodeId) -> Option<NodeId> {
    let r0 = next_sibling(doc, child);
    if r0 == Some(node) {
        next_sibling(doc, node)
    } else {
        r0
    }
}

/// The reference child of "replace" is a child of `parent` that is neither
/// `node` nor `child`, so it is still one after `child` is removed.
proof fn lemma_replace_reference(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        wf(doc),
        valid(doc, child),
        valid(doc, node),
        doc.nodes[child as int].parent == Some(parent),
    ensures
        match replace_reference(doc, child, node) {
            Some(r) => valid(doc, r) && r != node && r != child && doc.nodes[r as int].parent == Some(parent),
            None => true,
        },
{
    lemma_next_sibling(doc, child);
    let kids = children(doc, parent);
    let i = index_of(kids, child);
    if let Some(x) = next_sibling(doc, child) {
        if x == node {
            lemma_next_sibling(doc, node);
            assert(index_of(kids, node) == i + 1);
            if let Some(y) = next_sibling(doc, node) {
                assert(index_of(kids, y) == i + 2);
                assert(y != child);
            }
        }
    }
}

/// A call without an error from steps 1 to 6 of "replace" meets what
/// [`insert_any`] asks, after `child` is removed, with the reference child
/// of steps 7 and 8.
pub proof fn lemma_replace_valid(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        replace_error(doc, child, node, parent) is None,
    ensures
        super::contract::remove_requires(doc, child),
        insert_any_requires(remove(doc, child), node, parent, replace_reference(doc, child, node)),
        replace(doc, child, node, parent) == insert_any(remove(doc, child), node, parent, replace_reference(doc, child, node)),
{
    assert(doc.nodes[child as int].parent == Some(parent));
    let d1 = remove(doc, child);
    theorem_remove_wf(doc, child);
    theorem_remove_keeps_record(doc, child);
    lemma_not_host_not_incl(doc, node, parent);
    lemma_remove_ancestor_mono(doc, child, node, parent);
    lemma_replace_reference(doc, child, node, parent);
    if let Some(r) = replace_reference(doc, child, node) {
        assert(d1.nodes[r as int].parent == doc.nodes[r as int].parent);
    }
}

/// DOM §4.2.3† "replace" keeps the arena well formed. An error leaves it as
/// it is. Without one `child` has no parent afterwards (unless it is
/// `node`), and `node` (or a fragment's children) is a child of `parent`.
/// No kind or wrapper changes.
#[verifier::rlimit(50)]
pub proof fn theorem_replace_wf(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
    ensures
        wf(replace(doc, child, node, parent)),
        replace(doc, child, node, parent).nodes.len() == doc.nodes.len(),
        replace_error(doc, child, node, parent) is Some ==> replace(doc, child, node, parent) == doc,
        forall|x: int| #![trigger replace(doc, child, node, parent).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& replace(doc, child, node, parent).nodes[x].kind == doc.nodes[x].kind
            &&& replace(doc, child, node, parent).nodes[x].wrapper == doc.nodes[x].wrapper
        },
        replace_error(doc, child, node, parent) is None && child != node ==> replace(doc, child, node, parent).nodes[child as int].parent is None,
        replace_error(doc, child, node, parent) is None && !(doc.nodes[node as int].kind is DocumentFragment) ==>
            replace(doc, child, node, parent).nodes[node as int].parent == Some(parent),
        replace_error(doc, child, node, parent) is None && doc.nodes[node as int].kind is DocumentFragment ==> {
            &&& replace(doc, child, node, parent).nodes[node as int].children.len() == 0
            &&& forall|j: int| 0 <= j < doc.nodes[node as int].children.len() ==>
                replace(doc, child, node, parent).nodes[#[trigger] doc.nodes[node as int].children[j] as int].parent == Some(parent)
        },
{
    if replace_error(doc, child, node, parent) is None {
        lemma_replace_valid(doc, child, node, parent);
        let d1 = remove(doc, child);
        let r = replace_reference(doc, child, node);
        theorem_remove_wf(doc, child);
        theorem_remove_keeps_record(doc, child);
        theorem_insert_any_wf(d1, node, parent, r);
        let out = replace(doc, child, node, parent);
        assert(out == insert_any(d1, node, parent, r));
        let paths = lemma_wf_witness(d1);
        lemma_wf_split(d1, paths);
        if child != node && doc.nodes[node as int].kind is DocumentFragment {
            if d1.nodes[node as int].children.contains(child) {
                let j = choose|j: int| 0 <= j < d1.nodes[node as int].children.len() && d1.nodes[node as int].children[j] == child;
                assert(d1.nodes[node as int].children[j] == child);
                assert(d1.nodes[child as int].parent == Some(node));
            }
        }
        if doc.nodes[node as int].kind is DocumentFragment {
            // `node` is not `parent`, the only node whose children changed.
            assert(node != parent);
            assert(d1.nodes[node as int].children == doc.nodes[node as int].children);
        }
    }
}

// ---------------------------------------------------------------------
// replace all

/// A call meeting [`replace_all_requires`]: after step 5, the arena is well
/// formed, `parent` has no children, and `node` may be inserted.
pub proof fn lemma_replace_all_valid(doc: Document, node: Option<NodeId>, parent: NodeId)
    requires
        replace_all_requires(doc, node, parent),
    ensures
        ({
            let d1 = remove_children(doc, parent);
            &&& wf(d1)
            &&& d1.nodes.len() == doc.nodes.len()
            &&& d1.nodes[parent as int].children.len() == 0
            &&& forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d1.nodes[x]).kind == doc.nodes[x].kind && d1.nodes[x].wrapper
                == doc.nodes[x].wrapper
            &&& match node {
                None => true,
                Some(n) => insert_any_requires(d1, n, parent, None),
            }
        }),
{
    let kids = doc.nodes[parent as int].children;
    let len = kids.len();
    lemma_remove_children_n(doc, parent, len);
    let d1 = remove_children(doc, parent);
    assert(children(doc, parent) == kids);
    assert(d1.nodes == removed_prefix(doc, parent, len as int));
    assert(kids.subrange(len as int, len as int) =~= seq![]);
    assert(d1.nodes.len() == doc.nodes.len());
    assert forall|x: int| 0 <= x < doc.nodes.len() implies (#[trigger] d1.nodes[x]).kind == doc.nodes[x].kind && d1.nodes[x].wrapper
        == doc.nodes[x].wrapper by {}
    if let Some(n) = node {
        lemma_not_host_not_incl(doc, n, parent);
        lemma_remove_children_n_ancestors(doc, parent, len, n, parent);
    }
}

/// The records of [`removed_prefix`] for a node that is neither the parent
/// nor among the removed.
proof fn lemma_removed_prefix_other(d: Document, p: NodeId, k: int, x: NodeId)
    requires
        valid(d, p),
        valid(d, x),
        x != p,
        !d.nodes[p as int].children.subrange(0, k).contains(x),
    ensures
        removed_prefix(d, p, k)[x as int] == d.nodes[x as int],
{
}

/// The children of `parent` in [`fragment_inserted`].
proof fn lemma_fragment_inserted_parent(d: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        valid(d, frag),
        valid(d, parent),
        parent != frag,
    ensures
        fragment_inserted(d, frag, parent, child)[parent as int].children == list_kids(
            d.nodes[parent as int].children,
            d.nodes[frag as int].children,
            child,
        ),
{
}

/// "Replace all" with a fragment: `parent`'s children are the fragment's.
proof fn lemma_replace_all_fragment(doc: Document, n: NodeId, parent: NodeId)
    requires
        replace_all_requires(doc, Some(n), parent),
        doc.nodes[n as int].kind is DocumentFragment,
    ensures
        children(replace_all(doc, Some(n), parent), parent) == children(doc, n),
{
    lemma_replace_all_valid(doc, Some(n), parent);
    let d1 = remove_children(doc, parent);
    lemma_insert_fragment(d1, n, parent, None);
    let kids = d1.nodes[parent as int].children;
    let len = doc.nodes[parent as int].children.len();
    assert(kids =~= seq![]);
    assert(n != parent);
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
    lemma_remove_children_n(doc, parent, len);
    assert(children(doc, parent) == doc.nodes[parent as int].children);
    assert(!doc.nodes[parent as int].children.contains(n)) by {
        if doc.nodes[parent as int].children.contains(n) {
            let j = choose|j: int| 0 <= j < len && doc.nodes[parent as int].children[j] == n;
            assert(doc.nodes[n as int].parent == Some(parent));
        }
    }
    assert(doc.nodes[parent as int].children.subrange(0, len as int) =~= doc.nodes[parent as int].children);
    lemma_removed_prefix_other(doc, parent, len as int, n);
    assert(d1.nodes[n as int] == doc.nodes[n as int]);
    lemma_fragment_inserted_parent(d1, n, parent, None);
    assert(list_kids(kids, doc.nodes[n as int].children, None) =~= doc.nodes[n as int].children);
}

/// "Replace all" with a node that is not a fragment: `parent`'s children are
/// that node.
proof fn lemma_replace_all_node(doc: Document, n: NodeId, parent: NodeId)
    requires
        replace_all_requires(doc, Some(n), parent),
        !(doc.nodes[n as int].kind is DocumentFragment),
    ensures
        children(replace_all(doc, Some(n), parent), parent) == seq![n],
{
    lemma_replace_all_valid(doc, Some(n), parent);
    let d1 = remove_children(doc, parent);
    let paths = lemma_wf_witness(d1);
    assert(d1.nodes[n as int].kind == doc.nodes[n as int].kind);
    assert(insert_requires(d1, n, parent, None));
    theorem_insert_wf(d1, n, parent, None);
    let p0 = d1.nodes[n as int].parent;
    if p0 is Some {
        let q = p0->Some_0;
        assert(super::contract::remove_requires(d1, n));
        theorem_remove_keeps_record(d1, n);
        lemma_wf_split(d1, paths);
        assert(d1.nodes[q as int].children.contains(n));
        assert(q != parent);
        assert(adopt(d1, n).nodes[parent as int].children == d1.nodes[parent as int].children);
    }
    assert(adopt(d1, n).nodes[parent as int].children =~= seq![]);
    assert(insert_kids(d1, n, parent, None) =~= seq![n]);
}

/// DOM §4.2.3† "replace all" keeps the arena well formed. `parent`'s
/// children afterwards are none (no node), `node` alone, or a fragment's
/// children. No kind or wrapper changes.
pub proof fn theorem_replace_all_wf(doc: Document, node: Option<NodeId>, parent: NodeId)
    requires
        replace_all_requires(doc, node, parent),
    ensures
        wf(replace_all(doc, node, parent)),
        replace_all(doc, node, parent).nodes.len() == doc.nodes.len(),
        forall|x: int| #![trigger replace_all(doc, node, parent).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& replace_all(doc, node, parent).nodes[x].kind == doc.nodes[x].kind
            &&& replace_all(doc, node, parent).nodes[x].wrapper == doc.nodes[x].wrapper
        },
        node is None ==> children(replace_all(doc, node, parent), parent).len() == 0,
        node is Some && !(doc.nodes[node->Some_0 as int].kind is DocumentFragment) ==> children(replace_all(doc, node, parent), parent) == seq![node->Some_0],
        node is Some && doc.nodes[node->Some_0 as int].kind is DocumentFragment ==> children(replace_all(doc, node, parent), parent) == children(
            doc,
            node->Some_0,
        ),
{
    lemma_replace_all_valid(doc, node, parent);
    let d1 = remove_children(doc, parent);
    if let Some(n) = node {
        theorem_insert_any_wf(d1, n, parent, None);
        assert(d1.nodes[n as int].kind == doc.nodes[n as int].kind);
        if doc.nodes[n as int].kind is DocumentFragment {
            lemma_replace_all_fragment(doc, n, parent);
        } else {
            lemma_replace_all_node(doc, n, parent);
        }
    }
}

} // verus!
