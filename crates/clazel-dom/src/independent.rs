//! A second transcription of DOM §4.2.3 "insert" and "remove" (with §4.5
//! "adopt", which insert's step 7.1 calls), written from the DOM Standard's
//! text, commit snapshot `3c53f93a3e1fb11ef5bd38029b7a9c97baaf0177`
//! (<https://dom.spec.whatwg.org/commit-snapshots/3c53f93a3e1fb11ef5bd38029b7a9c97baaf0177/>),
//! not from `spec.rs`. `independent_equivalence.rs` proves it equal to
//! [`super::spec::insert`] and [`super::spec::remove`] on the parser's
//! class of calls.
//!
//! **What this is worth.** DOM §4.2.3 has no second body's text: no other
//! standard defines the node tree's mutation algorithms, so this is a
//! same-text transcription. It can catch a slip in `spec.rs` (an index
//! taken in the wrong list, a field left unchanged), not a misreading
//! both transcriptions share. The weight of evidence for these
//! operations is Phase 4 item 4.11's tree-construction suite
//! (html5lib-tests), which checks the trees they build.
//!
//! Differences in form from `spec.rs`, deliberate:
//! - Infra's "remove" from a list removes the items that match
//!   ([`ind_without`], every occurrence of the node), rather than the item
//!   at the node's index;
//! - DOM §4.2 "index" is "its number of preceding siblings"
//!   ([`ind_index`]: the length of the prefix before it);
//! - "insert … before child's index" splits the list there and puts the
//!   node between the two parts;
//! - the new arena is built record by record (`Seq::new`), not by updates.
//!
//! The same restrictions as `spec.rs` apply (the parser's calls): `node`
//! is not a `DocumentFragment` (insert's step 1 gives « node », steps 3
//! and 4 do nothing), and steps that only touch live ranges, slots,
//! observers, custom elements, and the insertion, removing and children
//! changed steps are not modelled (none changes the tree).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Infra §5.1 list "remove": every item of `list` that is `item` is
/// removed.
pub open spec fn ind_without(list: Seq<NodeId>, item: NodeId) -> Seq<NodeId>
    decreases list.len(),
{
    if list.len() == 0 {
        list
    } else if list[0] == item {
        ind_without(list.drop_first(), item)
    } else {
        seq![list[0]] + ind_without(list.drop_first(), item)
    }
}

/// DOM §4.2 "The index of an object is its number of preceding siblings,
/// or 0 if it has none": the number of items of `siblings` before `object`.
pub open spec fn ind_index(siblings: Seq<NodeId>, object: NodeId) -> nat
    decreases siblings.len(),
{
    if siblings.len() == 0 || siblings[0] == object {
        0
    } else {
        1 + ind_index(siblings.drop_first(), object)
    }
}

/// DOM §4.2.3 "remove a node node": "1. Let parent be node's parent.
/// 2. Assert: parent is non-null." … "7. Remove node from its parent's
/// children." A node is in its parent's children exactly when its parent
/// is that parent (§4.2), so node's parent becomes null.
pub open spec fn ind_remove(document: Document, node: NodeId) -> Document {
    // 1.
    let parent = document.nodes[node as int].parent->Some_0;
    Document {
        nodes: Seq::new(
            document.nodes.len(),
            |i: int|
                {
                    let n = document.nodes[i];
                    if i == node {
                        // node is no longer a child: its parent is null.
                        Node { parent: None, ..n }
                    } else if i == parent {
                        // 7.
                        Node { children: ind_without(n.children, node), ..n }
                    } else {
                        n
                    }
                },
        ),
    }
}

/// DOM §4.5 "adopt a node node into a document document": "1. Let
/// oldDocument be node's node document. 2. If node's parent is non-null,
/// then remove node. 3. If document is not oldDocument, …" (the document
/// is always node's own).
pub open spec fn ind_adopt(document: Document, node: NodeId) -> Document {
    if document.nodes[node as int].parent is Some {
        ind_remove(document, node)
    } else {
        document
    }
}

/// DOM §4.2.3 "insert a node node into a node parent before null or a
/// node child", for a node that is not a `DocumentFragment`: "1. Let
/// nodes be … « node »." "7. For each node in nodes, in tree order: 1.
/// Adopt node into parent's node document. 2. If child is null, then
/// append node to parent's children. 3. Otherwise, insert node into
/// parent's children before child's index." Node's parent is then parent.
pub open spec fn ind_insert(document: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Document {
    // 7.1
    let adopted = ind_adopt(document, node);
    let children = adopted.nodes[parent as int].children;
    let new_children = match child {
        // 7.2
        None => children + seq![node],
        // 7.3
        Some(c) => {
            let index = ind_index(children, c) as int;
            children.subrange(0, index) + seq![node] + children.subrange(index, children.len() as int)
        },
    };
    Document {
        nodes: Seq::new(
            adopted.nodes.len(),
            |i: int|
                {
                    let n = adopted.nodes[i];
                    if i == parent {
                        Node { children: new_children, ..n }
                    } else if i == node {
                        Node { parent: Some(parent), ..n }
                    } else {
                        n
                    }
                },
        ),
    }
}

} // verus!
