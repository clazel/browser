//! The independent transcription ([`super::independent`]) is equal to the
//! spec's "remove", "adopt" and "insert" on the parser's class of calls
//! ([`remove_requires`], [`insert_requires`]): well-formed arenas, where a
//! children list has no duplicates, so removing every occurrence of a node
//! is removing it at its index, and "number of preceding siblings" is its
//! index.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Removing an item that is not there changes nothing.
pub proof fn lemma_without_absent(s: Seq<NodeId>, x: NodeId)
    requires
        !s.contains(x),
    ensures
        ind_without(s, x) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s[0] != x);
        if s.drop_first().contains(x) {
            let k = choose|k: int| 0 <= k < s.drop_first().len() && s.drop_first()[k] == x;
            assert(s[k + 1] == x);
        }
        lemma_without_absent(s.drop_first(), x);
        assert(seq![s[0]] + s.drop_first() =~= s);
    }
}

/// In a list without duplicates, Infra's "remove" of an item is removing
/// it at its index.
pub proof fn lemma_without_is_remove(s: Seq<NodeId>, x: NodeId)
    requires
        s.no_duplicates(),
        s.contains(x),
    ensures
        ind_without(s, x) == s.remove(index_of(s, x)),
    decreases s.len(),
{
    let r = s.drop_first();
    assert(r.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < r.len() && 0 <= j < r.len() && i != j implies r[i] != r[j] by {
            assert(r[i] == s[i + 1] && r[j] == s[j + 1]);
        }
    }
    if s[0] == x {
        if r.contains(x) {
            let k = choose|k: int| 0 <= k < r.len() && r[k] == x;
            assert(s[k + 1] == x);
        }
        lemma_without_absent(r, x);
        assert(s.remove(0) =~= r);
    } else {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        assert(r[k - 1] == x);
        assert(r.contains(x));
        lemma_without_is_remove(r, x);
        lemma_index_of(r, x);
        let i = index_of(r, x);
        assert(index_of(s, x) == i + 1);
        assert(seq![s[0]] + r.remove(i) =~= s.remove(i + 1));
    }
}

/// "Number of preceding siblings" is [`index_of`] for a child.
pub proof fn lemma_ind_index(s: Seq<NodeId>, c: NodeId)
    requires
        s.contains(c),
    ensures
        ind_index(s, c) == index_of(s, c),
    decreases s.len(),
{
    if s[0] != c {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == c;
        assert(s.drop_first()[k - 1] == c);
        assert(s.drop_first().contains(c));
        lemma_ind_index(s.drop_first(), c);
        lemma_index_of(s.drop_first(), c);
    }
}

/// The independent "remove" is the spec's.
pub proof fn lemma_independent_remove(doc: Document, node: NodeId)
    requires
        remove_requires(doc, node),
    ensures
        ind_remove(doc, node) == remove(doc, node),
{
    let paths = lemma_wf_witness(doc);
    lemma_remove_nodes(doc, paths, node);
    let p = doc.nodes[node as int].parent->Some_0;
    let kids = doc.nodes[p as int].children;
    assert(kids.no_duplicates());
    lemma_index_of(kids, node);
    lemma_without_is_remove(kids, node);
    let a = ind_remove(doc, node);
    let b = remove(doc, node);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies #[trigger] a.nodes[i] == b.nodes[i] by {}
    assert(a.nodes =~= b.nodes);
}

/// The independent "adopt" is the spec's.
pub proof fn lemma_independent_adopt(doc: Document, node: NodeId)
    requires
        wf(doc),
        valid(doc, node),
    ensures
        ind_adopt(doc, node) == adopt(doc, node),
{
    if doc.nodes[node as int].parent is Some {
        lemma_independent_remove(doc, node);
    }
}

/// The independent "insert" is the spec's, on every call the parser makes
/// ([`insert_requires`]); so are "append" and "pre-insert", which call it.
pub proof fn lemma_independent_insert(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_requires(doc, node, parent, child),
    ensures
        ind_insert(doc, node, parent, child) == insert(doc, node, parent, child),
{
    let paths = lemma_wf_witness(doc);
    lemma_independent_adopt(doc, node);
    let d1 = adopt(doc, node);
    let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
    let kids1 = d1.nodes[parent as int].children;
    let kids = insert_kids(doc, node, parent, child);
    lemma_adopt(doc, paths, node, parent, child);
    lemma_insert_is_attach(doc, node, parent, child);
    lemma_insert_attach_requires(doc, paths, node, parent, child);
    lemma_attach_nodes(d1, p1, node, parent, kids);
    lemma_listed(d1, p1, node, parent, child);
    let new_children = match child {
        None => kids1 + seq![node],
        Some(c) => {
            let index = ind_index(kids1, c) as int;
            kids1.subrange(0, index) + seq![node] + kids1.subrange(index, kids1.len() as int)
        },
    };
    match child {
        None => {
            assert(new_children =~= kids);
        },
        Some(c) => {
            lemma_ind_index(kids1, c);
            lemma_index_of(kids1, c);
            assert(new_children =~= kids);
        },
    }
    let a = ind_insert(doc, node, parent, child);
    let b = insert(doc, node, parent, child);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies #[trigger] a.nodes[i] == b.nodes[i] by {}
    assert(a.nodes =~= b.nodes);
}

} // verus!
