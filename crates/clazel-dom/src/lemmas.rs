//! Facts proven about the spec (Phase 4 item 4.8): the acyclicity witness
//! of [`wf_with`] really is the chain of inclusive ancestors, and every
//! operation of [`super::spec`] keeps [`wf`] and does what its DOM steps say.
//!
//! The witness `paths` of a well-formed arena gives each node the sequence
//! of its inclusive ancestors from its root down to itself
//! ([`lemma_path`]); it has no duplicates and is at most `nodes.len()` long
//! ([`lemma_path_facts`]), so following parents ends within that many steps
//! and [`is_inclusive_ancestor`] is exactly membership in the path
//! ([`lemma_ancestor_iff_path`]). Each theorem builds the new witness
//! explicitly: removing a node drops its ancestors from the paths through
//! it ([`remove_paths`]), attaching a parentless node prepends its new
//! parent's path ([`attach_paths`]).
//!
//! The theorems the crate's `Cargo.toml` lists are `pub proof fn`s named
//! `theorem_*`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Sequences

/// [`index_of`] is the position of the first occurrence, or -1.
pub proof fn lemma_index_of(s: Seq<NodeId>, x: NodeId)
    ensures
        -1 <= index_of(s, x) < s.len(),
        index_of(s, x) >= 0 ==> s[index_of(s, x)] == x,
        index_of(s, x) >= 0 <==> s.contains(x),
        forall|j: int| 0 <= j < index_of(s, x) ==> s[j] != x,
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s[0] == x {
        assert(s.contains(x));
    } else {
        lemma_index_of(s.drop_first(), x);
        let r = index_of(s.drop_first(), x);
        if r >= 0 {
            assert(s[r + 1] == s.drop_first()[r]);
            assert(s.contains(x));
            assert forall|j: int| 0 <= j < r + 1 implies s[j] != x by {
                if j > 0 {
                    assert(s[j] == s.drop_first()[j - 1]);
                }
            }
        } else {
            if s.contains(x) {
                let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
                assert(k > 0);
                assert(s.drop_first()[k - 1] == x);
                assert(s.drop_first().contains(x));
            }
        }
    }
}

/// In a sequence without duplicates, the index of an element is its
/// position.
pub proof fn lemma_index_of_unique(s: Seq<NodeId>, k: int)
    requires
        s.no_duplicates(),
        0 <= k < s.len(),
    ensures
        index_of(s, s[k]) == k,
{
    lemma_index_of(s, s[k]);
    assert(s.contains(s[k]));
}

/// Inserting an element that is not there keeps a sequence free of
/// duplicates, and adds exactly that element.
pub proof fn lemma_seq_insert(s: Seq<NodeId>, k: int, y: NodeId)
    requires
        s.no_duplicates(),
        !s.contains(y),
        0 <= k <= s.len(),
    ensures
        s.insert(k, y).no_duplicates(),
        s.insert(k, y).len() == s.len() + 1,
        s.insert(k, y)[k] == y,
        forall|z: NodeId| #![trigger s.insert(k, y).contains(z)] #![trigger s.contains(z)] s.insert(k, y).contains(z) <==> (z == y || s.contains(z)),
        forall|j: int| #![trigger s.insert(k, y)[j]] 0 <= j < k ==> s.insert(k, y)[j] == s[j],
        forall|j: int| #![trigger s.insert(k, y)[j]] k < j <= s.len() ==> s.insert(k, y)[j] == s[j - 1],
{
    let t = s.insert(k, y);
    assert(t.len() == s.len() + 1);
    assert forall|j: int| 0 <= j < k implies t[j] == s[j] by {}
    assert forall|j: int| k < j <= s.len() implies t[j] == s[j - 1] by {}
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        if i != k && j != k {
            let si = if i < k { i } else { i - 1 };
            let sj = if j < k { j } else { j - 1 };
            assert(t[i] == s[si]);
            assert(t[j] == s[sj]);
        } else if i == k {
            let sj = if j < k { j } else { j - 1 };
            assert(t[j] == s[sj]);
        } else {
            let si = if i < k { i } else { i - 1 };
            assert(t[i] == s[si]);
        }
    }
    assert forall|z: NodeId| t.contains(z) <==> (z == y || s.contains(z)) by {
        if t.contains(z) {
            let i = choose|i: int| 0 <= i < t.len() && t[i] == z;
            if i < k {
                assert(s[i] == z);
            } else if i > k {
                assert(s[i - 1] == z);
            }
        }
        if z == y {
            assert(t[k] == z);
        }
        if s.contains(z) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == z;
            if i < k {
                assert(t[i] == z);
            } else {
                assert(t[i + 1] == z);
            }
        }
    }
}

/// Removing the element at `k` of a sequence without duplicates keeps it
/// free of duplicates and removes exactly that element.
pub proof fn lemma_seq_remove(s: Seq<NodeId>, k: int)
    requires
        s.no_duplicates(),
        0 <= k < s.len(),
    ensures
        s.remove(k).no_duplicates(),
        s.remove(k).len() == s.len() - 1,
        forall|z: NodeId| #![trigger s.remove(k).contains(z)] #![trigger s.contains(z)] s.remove(k).contains(z) <==> (z != s[k] && s.contains(z)),
        forall|j: int| #![trigger s.remove(k)[j]] 0 <= j < k ==> s.remove(k)[j] == s[j],
        forall|j: int| #![trigger s.remove(k)[j]] k <= j < s.len() - 1 ==> s.remove(k)[j] == s[j + 1],
{
    let t = s.remove(k);
    assert(t.len() == s.len() - 1);
    assert forall|j: int| 0 <= j < k implies t[j] == s[j] by {}
    assert forall|j: int| k <= j < s.len() - 1 implies t[j] == s[j + 1] by {}
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        let si = if i < k { i } else { i + 1 };
        let sj = if j < k { j } else { j + 1 };
        assert(t[i] == s[si]);
        assert(t[j] == s[sj]);
    }
    assert forall|z: NodeId| t.contains(z) <==> (z != s[k] && s.contains(z)) by {
        if t.contains(z) {
            let i = choose|i: int| 0 <= i < t.len() && t[i] == z;
            let si = if i < k { i } else { i + 1 };
            assert(t[i] == s[si]);
            assert(s.contains(z));
        }
        if z != s[k] && s.contains(z) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == z;
            if i < k {
                assert(t[i] == z);
            } else {
                assert(i != k);
                assert(t[i - 1] == z);
            }
        }
    }
}

/// Pigeonhole: a sequence without duplicates whose elements are below `n`
/// has at most `n` elements.
pub proof fn lemma_pigeonhole(s: Seq<NodeId>, n: nat)
    requires
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> (s[i] as nat) < n,
    ensures
        s.len() <= n,
    decreases n,
{
    if n == 0 {
        if s.len() > 0 {
            assert((s[0] as nat) < n);
        }
    } else if exists|k: int| 0 <= k < s.len() && s[k] as int == n - 1 {
        let k = choose|k: int| 0 <= k < s.len() && s[k] as int == n - 1;
        lemma_seq_remove(s, k);
        let t = s.remove(k);
        assert forall|i: int| 0 <= i < t.len() implies (t[i] as nat) < (n - 1) as nat by {
            let si = if i < k { i } else { i + 1 };
            assert(t[i] == s[si]);
            assert(si != k);
        }
        lemma_pigeonhole(t, (n - 1) as nat);
    } else {
        assert forall|i: int| 0 <= i < s.len() implies (s[i] as nat) < (n - 1) as nat by {
            assert((s[i] as nat) < n);
        }
        lemma_pigeonhole(s, (n - 1) as nat);
    }
}

// ---------------------------------------------------------------------
// The acyclicity witness

/// The path of `x` ends in `x`, its entries are nodes of the arena, and the
/// path of its `i`th entry is its prefix up to and including `i`: the path
/// is the chain of `x`'s inclusive ancestors from its root.
pub proof fn lemma_path(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, x),
    ensures
        paths[x as int].len() >= 1,
        paths[x as int].last() == x,
        forall|i: int|
            0 <= i < paths[x as int].len() ==> {
                &&& (#[trigger] paths[x as int][i]) < doc.nodes.len()
                &&& paths[paths[x as int][i] as int] == paths[x as int].subrange(0, i + 1)
            },
    decreases paths[x as int].len(),
{
    let px = paths[x as int];
    assert(px == match doc.nodes[x as int].parent {
        None => seq![x],
        Some(p) => paths[p as int].push(x),
    });
    match doc.nodes[x as int].parent {
        None => {
            assert forall|i: int| 0 <= i < px.len() implies {
                &&& (#[trigger] px[i]) < doc.nodes.len()
                &&& paths[px[i] as int] == px.subrange(0, i + 1)
            } by {
                assert(i == 0);
                assert(px.subrange(0, 1) =~= px);
            }
        },
        Some(p) => {
            assert(p < doc.nodes.len());
            let pp = paths[p as int];
            assert(px.len() == pp.len() + 1);
            lemma_path(doc, paths, p);
            assert forall|i: int| 0 <= i < px.len() implies {
                &&& (#[trigger] px[i]) < doc.nodes.len()
                &&& paths[px[i] as int] == px.subrange(0, i + 1)
            } by {
                if i < pp.len() {
                    assert(px[i] == pp[i]);
                    assert(px.subrange(0, i + 1) =~= pp.subrange(0, i + 1));
                } else {
                    assert(px.subrange(0, i + 1) =~= px);
                }
            }
        },
    }
}

/// A path has no duplicates, so it is at most as long as the arena.
pub proof fn lemma_path_facts(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, x),
    ensures
        paths[x as int].no_duplicates(),
        paths[x as int].len() <= doc.nodes.len(),
{
    lemma_path(doc, paths, x);
    let s = paths[x as int];
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {
        if s[i] == s[j] {
            assert(paths[s[i] as int] == s.subrange(0, i + 1));
            assert(paths[s[j] as int] == s.subrange(0, j + 1));
            assert(s.subrange(0, i + 1).len() != s.subrange(0, j + 1).len());
        }
    }
    assert forall|i: int| 0 <= i < s.len() implies (s[i] as nat) < doc.nodes.len() by {
        assert(s[i] < doc.nodes.len());
    }
    lemma_pigeonhole(s, doc.nodes.len());
}

/// If `a` is on the path of `x`, the path of `a` is a prefix of it, so the
/// path of every node on `a`'s path is on `x`'s too.
pub proof fn lemma_path_prefix(doc: Document, paths: Seq<Seq<NodeId>>, a: NodeId, x: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, x),
        paths[x as int].contains(a),
    ensures
        valid(doc, a),
        paths[a as int].len() <= paths[x as int].len(),
        forall|z: NodeId| paths[a as int].contains(z) ==> paths[x as int].contains(z),
        exists|k: int| 0 <= k < paths[x as int].len() && paths[x as int][k] == a && paths[a as int] == paths[x as int].subrange(0, k + 1),
{
    lemma_path(doc, paths, x);
    let k = choose|k: int| 0 <= k < paths[x as int].len() && paths[x as int][k] == a;
    assert(paths[x as int][k] < doc.nodes.len());
    assert(paths[a as int] == paths[x as int].subrange(0, k + 1));
    assert forall|z: NodeId| paths[a as int].contains(z) implies paths[x as int].contains(z) by {
        let j = choose|j: int| 0 <= j < paths[a as int].len() && paths[a as int][j] == z;
        assert(paths[x as int][j] == z);
    }
}

/// Following parents from `x` for `fuel` steps, with enough fuel, meets
/// exactly the nodes on its path.
pub proof fn lemma_within_iff_path(doc: Document, paths: Seq<Seq<NodeId>>, a: NodeId, x: NodeId, fuel: nat)
    requires
        wf_with(doc, paths),
        valid(doc, x),
        fuel + 1 >= paths[x as int].len(),
    ensures
        inclusive_ancestor_within(doc, a, x, fuel) <==> paths[x as int].contains(a),
    decreases fuel,
{
    lemma_path(doc, paths, x);
    let px = paths[x as int];
    assert(px[px.len() - 1] == x);
    assert(px == match doc.nodes[x as int].parent {
        None => seq![x],
        Some(p) => paths[p as int].push(x),
    });
    if x == a {
        assert(px.contains(a));
    } else if fuel == 0 {
        if px.contains(a) {
            let i = choose|i: int| 0 <= i < px.len() && px[i] == a;
            assert(i == px.len() - 1);
        }
    } else {
        match doc.nodes[x as int].parent {
            None => {
                if px.contains(a) {
                    let i = choose|i: int| 0 <= i < px.len() && px[i] == a;
                    assert(i == 0);
                }
            },
            Some(p) => {
                assert(p < doc.nodes.len());
                let pp = paths[p as int];
                lemma_within_iff_path(doc, paths, a, p, (fuel - 1) as nat);
                if px.contains(a) {
                    let i = choose|i: int| 0 <= i < px.len() && px[i] == a;
                    assert(i < pp.len());
                    assert(pp[i] == a);
                }
                if pp.contains(a) {
                    let i = choose|i: int| 0 <= i < pp.len() && pp[i] == a;
                    assert(px[i] == a);
                }
            },
        }
    }
}

/// DOM §4.2 "inclusive ancestor" in a well-formed arena is membership in
/// the witness path, whatever the witness.
pub proof fn lemma_ancestor_iff_path(doc: Document, paths: Seq<Seq<NodeId>>, a: NodeId, x: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, x),
    ensures
        is_inclusive_ancestor(doc, a, x) <==> paths[x as int].contains(a),
{
    lemma_path_facts(doc, paths, x);
    lemma_within_iff_path(doc, paths, a, x, doc.nodes.len());
}

/// A node is not its own parent.
pub proof fn lemma_parent_not_self(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, x),
    ensures
        doc.nodes[x as int].parent != Some(x),
{
    if doc.nodes[x as int].parent == Some(x) {
        assert(paths[x as int] == paths[x as int].push(x));
        assert(paths[x as int].len() == paths[x as int].push(x).len());
    }
}

/// The witness is unique: two witnesses of one arena are equal.
pub proof fn lemma_paths_unique(doc: Document, p1: Seq<Seq<NodeId>>, p2: Seq<Seq<NodeId>>)
    requires
        wf_with(doc, p1),
        wf_with(doc, p2),
    ensures
        p1 == p2,
{
    assert forall|x: int| 0 <= x < doc.nodes.len() implies p1[x] == p2[x] by {
        lemma_paths_unique_at(doc, p1, p2, x as NodeId);
    }
    assert(p1 =~= p2);
}

/// [`lemma_paths_unique`] at one node, by induction on its path.
pub proof fn lemma_paths_unique_at(doc: Document, p1: Seq<Seq<NodeId>>, p2: Seq<Seq<NodeId>>, x: NodeId)
    requires
        wf_with(doc, p1),
        wf_with(doc, p2),
        valid(doc, x),
    ensures
        p1[x as int] == p2[x as int],
    decreases p1[x as int].len(),
{
    assert(p1[x as int] == match doc.nodes[x as int].parent {
        None => seq![x],
        Some(p) => p1[p as int].push(x),
    });
    assert(p2[x as int] == match doc.nodes[x as int].parent {
        None => seq![x],
        Some(p) => p2[p as int].push(x),
    });
    match doc.nodes[x as int].parent {
        None => {},
        Some(p) => {
            assert(p < doc.nodes.len());
            assert(p1[x as int].len() == p1[p as int].len() + 1);
            lemma_paths_unique_at(doc, p1, p2, p);
        },
    }
}

// ---------------------------------------------------------------------
// wf in three parts

/// The conjuncts of [`wf_with`] about kinds: the size, the document node,
/// templates and their contents, form owners.
pub open spec fn wf_kinds(doc: Document) -> bool {
    let n = doc.nodes.len();
    &&& 1 <= n <= max_nodes()
    &&& doc.nodes[0].kind is Document
    &&& forall|i: int| 0 < i < n ==> !(#[trigger] doc.nodes[i].kind is Document)
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is Element && doc.nodes[i].kind->Element_template_contents is Some ==> {
        let f = doc.nodes[i].kind->Element_template_contents->Some_0;
        &&& f < n
        &&& doc.nodes[f as int].kind is DocumentFragment
        &&& doc.nodes[f as int].kind->DocumentFragment_host == Some(i as NodeId)
    }
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is DocumentFragment && doc.nodes[i].kind->DocumentFragment_host is Some ==> {
        let h = doc.nodes[i].kind->DocumentFragment_host->Some_0;
        &&& h < n
        &&& doc.nodes[h as int].kind is Element
        &&& doc.nodes[h as int].kind->Element_template_contents == Some(i as NodeId)
    }
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is Element && doc.nodes[i].kind->Element_form_owner is Some ==>
        doc.nodes[i].kind->Element_form_owner->Some_0 < n
}

/// The conjuncts of [`wf_with`] about parents and children.
pub open spec fn wf_links(doc: Document) -> bool {
    let n = doc.nodes.len();
    &&& doc.nodes[0].parent is None
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).parent is Some ==> {
        let p = doc.nodes[i].parent->Some_0;
        &&& p < n
        &&& doc.nodes[p as int].children.contains(i as NodeId)
    }
    &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < doc.nodes[i].children.len() ==> {
        let c = (#[trigger] doc.nodes[i].children[j]);
        &&& c < n
        &&& doc.nodes[c as int].parent == Some(i as NodeId)
    }
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] doc.nodes[i]).children.no_duplicates()
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).children.len() > 0 ==> may_have_children(doc.nodes[i].kind)
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is DocumentFragment ==> doc.nodes[i].parent is None
}

/// The acyclicity conjuncts of [`wf_with`].
pub open spec fn wf_paths(doc: Document, paths: Seq<Seq<NodeId>>) -> bool {
    let n = doc.nodes.len();
    &&& paths.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] paths[i] == match doc.nodes[i].parent {
        None => seq![i as NodeId],
        Some(p) => paths[p as int].push(i as NodeId),
    }
}

/// [`wf_with`] is the three parts.
pub proof fn lemma_wf_split(doc: Document, paths: Seq<Seq<NodeId>>)
    ensures
        wf_with(doc, paths) == (wf_kinds(doc) && wf_links(doc) && wf_paths(doc, paths)),
{
}

/// The kinds part only reads kinds.
pub proof fn lemma_kinds_frame(doc: Document, d: Document)
    requires
        wf_kinds(doc),
        d.nodes.len() == doc.nodes.len(),
        forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d.nodes[x]).kind == doc.nodes[x].kind,
    ensures
        wf_kinds(d),
{
    let n = doc.nodes.len();
    assert(d.nodes[0].kind == doc.nodes[0].kind);
    assert forall|x: int| 0 < x < n implies !(#[trigger] d.nodes[x].kind is Document) by {
        assert(d.nodes[x].kind == doc.nodes[x].kind);
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_template_contents is Some implies {
        let f = d.nodes[x].kind->Element_template_contents->Some_0;
        &&& f < n
        &&& d.nodes[f as int].kind is DocumentFragment
        &&& d.nodes[f as int].kind->DocumentFragment_host == Some(x as NodeId)
    } by {
        assert(doc.nodes[x].kind is Element);
        let f = doc.nodes[x].kind->Element_template_contents->Some_0;
        assert(d.nodes[f as int].kind == doc.nodes[f as int].kind);
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).kind is DocumentFragment && d.nodes[x].kind->DocumentFragment_host is Some implies {
        let h = d.nodes[x].kind->DocumentFragment_host->Some_0;
        &&& h < n
        &&& d.nodes[h as int].kind is Element
        &&& d.nodes[h as int].kind->Element_template_contents == Some(x as NodeId)
    } by {
        assert(doc.nodes[x].kind is DocumentFragment);
        let h = doc.nodes[x].kind->DocumentFragment_host->Some_0;
        assert(d.nodes[h as int].kind == doc.nodes[h as int].kind);
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_form_owner is Some implies
        d.nodes[x].kind->Element_form_owner->Some_0 < n by {
        assert(doc.nodes[x].kind is Element);
    }
}

// ---------------------------------------------------------------------
// remove

/// The witness after removing `node` from its parent: every path through
/// `node` loses the ancestors above it, so it starts at `node`.
pub open spec fn remove_paths(paths: Seq<Seq<NodeId>>, node: NodeId) -> Seq<Seq<NodeId>> {
    Seq::new(
        paths.len(),
        |x: int|
            if paths[x].contains(node) {
                paths[x].subrange(paths[node as int].len() - 1, paths[x].len() as int)
            } else {
                paths[x]
            },
    )
}

/// What [`remove`] does to each record: `node` loses its parent, its parent
/// loses it from its children (at its index), and nothing else changes.
pub proof fn lemma_remove_nodes(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        ({
            let p = doc.nodes[node as int].parent->Some_0;
            let kids = doc.nodes[p as int].children;
            let i = index_of(kids, node);
            let d = remove(doc, node);
            &&& valid(doc, p)
            &&& p != node
            &&& node != 0
            &&& 0 <= i < kids.len()
            &&& kids[i] == node
            &&& d.nodes.len() == doc.nodes.len()
            &&& forall|x: int| #![trigger d.nodes[x]] 0 <= x < doc.nodes.len() ==> d.nodes[x] == (if x == node {
                Node { parent: None, ..doc.nodes[x] }
            } else if x == p {
                Node { children: kids.remove(i), ..doc.nodes[x] }
            } else {
                doc.nodes[x]
            })
        }),
{
    let p = doc.nodes[node as int].parent->Some_0;
    assert(p < doc.nodes.len());
    assert(doc.nodes[p as int].children.contains(node));
    lemma_parent_not_self(doc, paths, node);
    lemma_index_of(doc.nodes[p as int].children, node);
}

/// [`remove`]: every parent lists its child.
pub proof fn lemma_remove_links_up(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        ({
            let d = remove(doc, node);
            forall|x: int| 0 <= x < d.nodes.len() && (#[trigger] d.nodes[x]).parent is Some ==> {
                let r = d.nodes[x].parent->Some_0;
                &&& r < d.nodes.len()
                &&& d.nodes[r as int].children.contains(x as NodeId)
            }
        }),
{
    let n = doc.nodes.len();
    let p = doc.nodes[node as int].parent->Some_0;
    let kids = doc.nodes[p as int].children;
    let i = index_of(kids, node);
    let d = remove(doc, node);
    lemma_remove_nodes(doc, paths, node);
    assert(kids.no_duplicates());
    lemma_seq_remove(kids, i);
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).parent is Some implies {
        let r = d.nodes[x].parent->Some_0;
        &&& r < n
        &&& d.nodes[r as int].children.contains(x as NodeId)
    } by {
        assert(doc.nodes[x].parent is Some);
        let r = doc.nodes[x].parent->Some_0;
        assert(doc.nodes[r as int].children.contains(x as NodeId));
    }
}

/// [`remove`]: every child has its parent.
pub proof fn lemma_remove_links_down(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        ({
            let d = remove(doc, node);
            forall|x: int, j: int| 0 <= x < d.nodes.len() && 0 <= j < d.nodes[x].children.len() ==> {
                let c = (#[trigger] d.nodes[x].children[j]);
                &&& c < d.nodes.len()
                &&& d.nodes[c as int].parent == Some(x as NodeId)
            }
        }),
{
    let n = doc.nodes.len();
    let p = doc.nodes[node as int].parent->Some_0;
    let kids = doc.nodes[p as int].children;
    let i = index_of(kids, node);
    let d = remove(doc, node);
    lemma_remove_nodes(doc, paths, node);
    assert(kids.no_duplicates());
    lemma_seq_remove(kids, i);
    assert forall|x: int, j: int| 0 <= x < n && 0 <= j < d.nodes[x].children.len() implies {
        let c = (#[trigger] d.nodes[x].children[j]);
        &&& c < n
        &&& d.nodes[c as int].parent == Some(x as NodeId)
    } by {
        let c = d.nodes[x].children[j];
        if x == p {
            let oj = if j < i { j } else { j + 1 };
            assert(c == kids[oj]);
            assert(kids[oj] != node);
            assert(doc.nodes[p as int].children[oj] == c);
        } else {
            assert(doc.nodes[x].children[j] == c);
            if c == node {
                assert(doc.nodes[c as int].parent == Some(x as NodeId));
            }
        }
    }
}

/// [`remove`] keeps the parent and children links consistent.
pub proof fn lemma_remove_links(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        wf_links(remove(doc, node)),
{
    let n = doc.nodes.len();
    let p = doc.nodes[node as int].parent->Some_0;
    let kids = doc.nodes[p as int].children;
    let i = index_of(kids, node);
    let d = remove(doc, node);
    lemma_remove_nodes(doc, paths, node);
    assert(kids.no_duplicates());
    lemma_seq_remove(kids, i);
    lemma_remove_links_up(doc, paths, node);
    lemma_remove_links_down(doc, paths, node);
    assert forall|x: int| 0 <= x < n implies (#[trigger] d.nodes[x]).children.no_duplicates() by {
        assert(doc.nodes[x].children.no_duplicates());
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).children.len() > 0 implies may_have_children(d.nodes[x].kind) by {
        assert(doc.nodes[x].children.len() > 0);
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] d.nodes[x]).kind is DocumentFragment implies d.nodes[x].parent is None by {
        assert(doc.nodes[x].kind is DocumentFragment);
    }
}

/// [`remove_paths`] along one parent edge `r` to `x`, as sequences.
pub proof fn lemma_remove_paths_step(paths: Seq<Seq<NodeId>>, node: NodeId, x: NodeId, r: NodeId)
    requires
        x < paths.len(),
        r < paths.len(),
        node < paths.len(),
        x != node,
        paths[x as int] == paths[r as int].push(x),
        forall|i: int| 0 <= i < paths[r as int].len() ==> paths[#[trigger] paths[r as int][i] as int] == paths[r as int].subrange(0, i + 1),
    ensures
        remove_paths(paths, node)[x as int] == remove_paths(paths, node)[r as int].push(x),
{
    let q = remove_paths(paths, node);
    let px = paths[x as int];
    let pr = paths[r as int];
    let ln = paths[node as int].len();
    assert(px[pr.len() as int] == x);
    if px.contains(node) {
        let k = choose|k: int| 0 <= k < px.len() && px[k] == node;
        assert(k < pr.len());
        assert(pr[k] == node);
        assert(pr.contains(node));
        assert(paths[pr[k] as int] == pr.subrange(0, k + 1));
        assert(ln == k + 1);
        assert(q[x as int] =~= q[r as int].push(x));
    } else {
        if pr.contains(node) {
            let k = choose|k: int| 0 <= k < pr.len() && pr[k] == node;
            assert(px[k] == node);
        }
    }
}

/// [`remove_paths`] at one node.
pub proof fn lemma_remove_paths_at(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId, x: int)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
        0 <= x < doc.nodes.len(),
    ensures
        remove_paths(paths, node)[x] == match remove(doc, node).nodes[x].parent {
            None => seq![x as NodeId],
            Some(r) => remove_paths(paths, node)[r as int].push(x as NodeId),
        },
{
    let n = doc.nodes.len();
    let d = remove(doc, node);
    let q = remove_paths(paths, node);
    lemma_remove_nodes(doc, paths, node);
    let px = paths[x];
    assert(px == match doc.nodes[x].parent {
        None => seq![x as NodeId],
        Some(r) => paths[r as int].push(x as NodeId),
    });
    if x == node as int {
        lemma_path(doc, paths, node);
        assert(px[px.len() - 1] == node);
        assert(px.contains(node));
        assert(q[x] =~= seq![x as NodeId]);
    } else {
        assert(d.nodes[x].parent == doc.nodes[x].parent);
        match doc.nodes[x].parent {
            None => {
                if px.contains(node) {
                    let k = choose|k: int| 0 <= k < px.len() && px[k] == node;
                    assert(k == 0);
                }
            },
            Some(r) => {
                assert(r < n);
                lemma_path(doc, paths, r);
                lemma_remove_paths_step(paths, node, x as NodeId, r);
            },
        }
    }
}

/// [`remove_paths`] is a witness for [`remove`]; paths that do not pass
/// through `node` are unchanged.
pub proof fn lemma_remove_paths(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        wf_paths(remove(doc, node), remove_paths(paths, node)),
        forall|x: int|
            0 <= x < doc.nodes.len() && !paths[x].contains(node) ==> #[trigger] remove_paths(paths, node)[x] == paths[x],
{
    let n = doc.nodes.len();
    let d = remove(doc, node);
    let q = remove_paths(paths, node);
    lemma_remove_nodes(doc, paths, node);
    assert forall|x: int| 0 <= x < n implies #[trigger] q[x] == match d.nodes[x].parent {
        None => seq![x as NodeId],
        Some(r) => q[r as int].push(x as NodeId),
    } by {
        lemma_remove_paths_at(doc, paths, node, x);
    }
}

/// [`remove`] keeps the arena well formed, with [`remove_paths`] as the new
/// witness; paths that do not pass through `node` are unchanged.
pub proof fn lemma_remove_wf_with(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId)
    requires
        wf_with(doc, paths),
        valid(doc, node),
        doc.nodes[node as int].parent is Some,
    ensures
        wf_with(remove(doc, node), remove_paths(paths, node)),
        forall|x: int|
            0 <= x < doc.nodes.len() && !paths[x].contains(node) ==> #[trigger] remove_paths(paths, node)[x] == paths[x],
{
    let d = remove(doc, node);
    lemma_remove_nodes(doc, paths, node);
    lemma_wf_split(doc, paths);
    lemma_kinds_frame(doc, d);
    lemma_remove_links(doc, paths, node);
    lemma_remove_paths(doc, paths, node);
    lemma_wf_split(d, remove_paths(paths, node));
}

// ---------------------------------------------------------------------
// insert

/// Steps 7.2 to 7.3 of DOM "insert" after step 7.1 has left `node` without
/// a parent: `parent`'s children become `kids`, and `node`'s parent becomes
/// `parent`.
pub open spec fn attach(d: Document, node: NodeId, parent: NodeId, kids: Seq<NodeId>) -> Document {
    let pn = d.nodes[parent as int];
    Document {
        nodes: d.nodes.update(parent as int, Node { children: kids, ..pn }).update(
            node as int,
            Node { parent: Some(parent), ..d.nodes[node as int] },
        ),
    }
}

/// The witness after attaching a parentless `node` to `parent`: every path
/// through `node` (which starts at `node`) is prefixed by `parent`'s path.
pub open spec fn attach_paths(paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId) -> Seq<Seq<NodeId>> {
    Seq::new(
        paths.len(),
        |x: int|
            if paths[x].contains(node) {
                paths[parent as int] + paths[x]
            } else {
                paths[x]
            },
    )
}

/// When [`attach`] keeps an arena well formed: `node` has no parent, is
/// not a document or a fragment, is not on `parent`'s path, and `kids` is
/// `parent`'s children with `node` added.
pub open spec fn attach_requires(d: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, kids: Seq<NodeId>) -> bool {
    &&& wf_with(d, paths)
    &&& valid(d, node)
    &&& valid(d, parent)
    &&& d.nodes[node as int].parent is None
    &&& !(d.nodes[node as int].kind is Document)
    &&& !(d.nodes[node as int].kind is DocumentFragment)
    &&& may_have_children(d.nodes[parent as int].kind)
    &&& !paths[parent as int].contains(node)
    &&& kids.no_duplicates()
    &&& forall|y: NodeId| #[trigger] kids.contains(y) <==> (y == node || d.nodes[parent as int].children.contains(y))
}

/// What [`attach`] does to each record.
pub proof fn lemma_attach_nodes(d: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_requires(d, paths, node, parent, kids),
    ensures
        node != parent,
        node != 0,
        !d.nodes[parent as int].children.contains(node),
        attach(d, node, parent, kids).nodes.len() == d.nodes.len(),
        forall|x: int| #![trigger attach(d, node, parent, kids).nodes[x]] 0 <= x < d.nodes.len() ==> attach(d, node, parent, kids).nodes[x] == (if x == node {
            Node { parent: Some(parent), ..d.nodes[x] }
        } else if x == parent {
            Node { children: kids, ..d.nodes[x] }
        } else {
            d.nodes[x]
        }),
{
    lemma_path(d, paths, parent);
    assert(paths[parent as int][paths[parent as int].len() - 1] == parent);
    if node == parent {
        assert(paths[parent as int].contains(node));
    }
    if d.nodes[parent as int].children.contains(node) {
        let j = choose|j: int| 0 <= j < d.nodes[parent as int].children.len() && d.nodes[parent as int].children[j] == node;
        assert(d.nodes[parent as int].children[j] == node);
    }
}

/// The facts about [`attach`]'s arguments its links part needs.
pub open spec fn attach_links_requires(d: Document, node: NodeId, parent: NodeId, kids: Seq<NodeId>) -> bool {
    &&& wf_links(d)
    &&& valid(d, node)
    &&& valid(d, parent)
    &&& node != parent
    &&& node != 0
    &&& d.nodes[node as int].parent is None
    &&& !(d.nodes[node as int].kind is DocumentFragment)
    &&& may_have_children(d.nodes[parent as int].kind)
    &&& kids.no_duplicates()
    &&& forall|y: NodeId| #[trigger] kids.contains(y) <==> (y == node || d.nodes[parent as int].children.contains(y))
    &&& attach(d, node, parent, kids).nodes.len() == d.nodes.len()
    &&& forall|x: int| #![trigger attach(d, node, parent, kids).nodes[x]] 0 <= x < d.nodes.len() ==> attach(d, node, parent, kids).nodes[x] == (if x == node {
        Node { parent: Some(parent), ..d.nodes[x] }
    } else if x == parent {
        Node { children: kids, ..d.nodes[x] }
    } else {
        d.nodes[x]
    })
}

/// [`attach`]: every parent lists its child.
pub proof fn lemma_attach_links_up(d: Document, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_links_requires(d, node, parent, kids),
    ensures
        ({
            let e = attach(d, node, parent, kids);
            forall|x: int| 0 <= x < e.nodes.len() && (#[trigger] e.nodes[x]).parent is Some ==> {
                let r = e.nodes[x].parent->Some_0;
                &&& r < e.nodes.len()
                &&& e.nodes[r as int].children.contains(x as NodeId)
            }
        }),
{
    let n = d.nodes.len();
    let e = attach(d, node, parent, kids);
    assert forall|x: int| 0 <= x < n && (#[trigger] e.nodes[x]).parent is Some implies {
        let r = e.nodes[x].parent->Some_0;
        &&& r < n
        &&& e.nodes[r as int].children.contains(x as NodeId)
    } by {
        if x == node {
            assert(kids.contains(node));
        } else {
            assert(d.nodes[x].parent is Some);
            let r = d.nodes[x].parent->Some_0;
            assert(d.nodes[r as int].children.contains(x as NodeId));
            if r == parent {
                assert(kids.contains(x as NodeId));
            }
        }
    }
}

/// [`attach`]: every child has its parent.
pub proof fn lemma_attach_links_down(d: Document, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_links_requires(d, node, parent, kids),
    ensures
        ({
            let e = attach(d, node, parent, kids);
            forall|x: int, j: int| 0 <= x < e.nodes.len() && 0 <= j < e.nodes[x].children.len() ==> {
                let c = (#[trigger] e.nodes[x].children[j]);
                &&& c < e.nodes.len()
                &&& e.nodes[c as int].parent == Some(x as NodeId)
            }
        }),
{
    let n = d.nodes.len();
    let e = attach(d, node, parent, kids);
    assert forall|x: int, j: int| 0 <= x < n && 0 <= j < e.nodes[x].children.len() implies {
        let c = (#[trigger] e.nodes[x].children[j]);
        &&& c < n
        &&& e.nodes[c as int].parent == Some(x as NodeId)
    } by {
        let c = e.nodes[x].children[j];
        if x == parent {
            assert(kids[j] == c);
            assert(kids.contains(c));
            if c != node {
                assert(d.nodes[parent as int].children.contains(c));
                let k = choose|k: int| 0 <= k < d.nodes[parent as int].children.len() && d.nodes[parent as int].children[k] == c;
                assert(d.nodes[parent as int].children[k] == c);
            }
        } else {
            assert(d.nodes[x].children[j] == c);
        }
    }
}

/// [`attach`] keeps the links consistent.
pub proof fn lemma_attach_links(d: Document, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_links_requires(d, node, parent, kids),
    ensures
        wf_links(attach(d, node, parent, kids)),
{
    let n = d.nodes.len();
    let e = attach(d, node, parent, kids);
    lemma_attach_links_up(d, node, parent, kids);
    lemma_attach_links_down(d, node, parent, kids);
    assert(e.nodes[0].parent == d.nodes[0].parent);
    assert forall|x: int| 0 <= x < n implies (#[trigger] e.nodes[x]).children.no_duplicates() by {
        assert(d.nodes[x].children.no_duplicates());
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] e.nodes[x]).children.len() > 0 implies may_have_children(e.nodes[x].kind) by {
        assert(d.nodes[x].kind == e.nodes[x].kind);
        if x != parent {
            assert(d.nodes[x].children.len() > 0);
        }
    }
    assert forall|x: int| 0 <= x < n && (#[trigger] e.nodes[x]).kind is DocumentFragment implies e.nodes[x].parent is None by {
        assert(d.nodes[x].kind is DocumentFragment);
    }
}

/// [`attach_paths`] is a witness for [`attach`]; paths that do not pass
/// through `node` are unchanged.
pub proof fn lemma_attach_paths(d: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_requires(d, paths, node, parent, kids),
    ensures
        wf_paths(attach(d, node, parent, kids), attach_paths(paths, node, parent)),
        forall|x: int|
            0 <= x < d.nodes.len() && !paths[x].contains(node) ==> #[trigger] attach_paths(paths, node, parent)[x] == paths[x],
{
    let n = d.nodes.len();
    let e = attach(d, node, parent, kids);
    let q = attach_paths(paths, node, parent);
    lemma_attach_nodes(d, paths, node, parent, kids);
    assert forall|x: int| 0 <= x < n implies #[trigger] q[x] == match e.nodes[x].parent {
        None => seq![x as NodeId],
        Some(r) => q[r as int].push(x as NodeId),
    } by {
        let px = paths[x];
        assert(px == match d.nodes[x].parent {
            None => seq![x as NodeId],
            Some(r) => paths[r as int].push(x as NodeId),
        });
        if x == node as int {
            assert(px == seq![node]);
            assert(px[0] == node);
            assert(px.contains(node));
            assert(q[parent as int] == paths[parent as int]);
            assert(q[x] =~= q[parent as int].push(x as NodeId));
        } else {
            match d.nodes[x].parent {
                None => {
                    if px.contains(node) {
                        let k = choose|k: int| 0 <= k < px.len() && px[k] == node;
                        assert(k == 0);
                    }
                },
                Some(r) => {
                    assert(r < n);
                    let pr = paths[r as int];
                    assert(px.len() == pr.len() + 1);
                    if px.contains(node) {
                        let k = choose|k: int| 0 <= k < px.len() && px[k] == node;
                        assert(k < pr.len());
                        assert(pr[k] == node);
                        assert(pr.contains(node));
                        assert(q[x] =~= q[r as int].push(x as NodeId));
                    } else {
                        if pr.contains(node) {
                            let k = choose|k: int| 0 <= k < pr.len() && pr[k] == node;
                            assert(px[k] == node);
                        }
                    }
                },
            }
        }
    }
}

/// [`attach`] keeps the arena well formed.
pub proof fn lemma_attach_wf_with(d: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, kids: Seq<NodeId>)
    requires
        attach_requires(d, paths, node, parent, kids),
    ensures
        wf_with(attach(d, node, parent, kids), attach_paths(paths, node, parent)),
        forall|x: int|
            0 <= x < d.nodes.len() && !paths[x].contains(node) ==> #[trigger] attach_paths(paths, node, parent)[x] == paths[x],
{
    let e = attach(d, node, parent, kids);
    lemma_attach_nodes(d, paths, node, parent, kids);
    lemma_wf_split(d, paths);
    lemma_kinds_frame(d, e);
    lemma_attach_links(d, node, parent, kids);
    lemma_attach_paths(d, paths, node, parent, kids);
    lemma_wf_split(e, attach_paths(paths, node, parent));
}

/// The witness after [`insert`]: [`remove_paths`] if `node` had a parent
/// (step 7.1), then [`attach_paths`].
pub open spec fn insert_paths(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId) -> Seq<Seq<NodeId>> {
    let p1 = if doc.nodes[node as int].parent is Some {
        remove_paths(paths, node)
    } else {
        paths
    };
    attach_paths(p1, node, parent)
}

/// `node` added to `kids1` as steps 7.2 and 7.3 of "insert" add it:
/// at the end, or before `child`.
pub open spec fn insert_into(kids1: Seq<NodeId>, node: NodeId, child: Option<NodeId>) -> Seq<NodeId> {
    match child {
        None => kids1.push(node),
        Some(c) => kids1.insert(index_of(kids1, c), node),
    }
}

/// The children `parent` gets in [`insert`].
pub open spec fn insert_kids(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Seq<NodeId> {
    insert_into(adopt(doc, node).nodes[parent as int].children, node, child)
}

/// Step 7.1 of "insert" ([`adopt`]) keeps the arena well formed, leaves
/// `node` without a parent, changes no kind, and leaves `parent`'s path
/// alone; `child`, if any, is still a child of `parent`.
pub proof fn lemma_adopt(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_requires(doc, node, parent, child),
        wf_with(doc, paths),
    ensures
        ({
            let d1 = adopt(doc, node);
            let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
            &&& wf_with(d1, p1)
            &&& d1.nodes.len() == doc.nodes.len()
            &&& forall|x: int| #![trigger d1.nodes[x]] 0 <= x < doc.nodes.len() ==> d1.nodes[x].kind == doc.nodes[x].kind
                && d1.nodes[x].wrapper == doc.nodes[x].wrapper
                && (x != node ==> d1.nodes[x].parent == doc.nodes[x].parent)
            &&& d1.nodes[node as int].parent is None
            &&& !paths[parent as int].contains(node)
            &&& p1[parent as int] == paths[parent as int]
            &&& forall|x: int| 0 <= x < doc.nodes.len() && !paths[x].contains(node) ==> #[trigger] p1[x] == paths[x]
            &&& match child {
                None => true,
                Some(c) => d1.nodes[c as int].parent == Some(parent),
            }
        }),
{
    lemma_ancestor_iff_path(doc, paths, node, parent);
    if doc.nodes[node as int].parent is Some {
        lemma_remove_nodes(doc, paths, node);
        lemma_remove_wf_with(doc, paths, node);
    }
}

/// [`insert`] is step 7.1 ([`adopt`]) followed by [`attach`].
pub proof fn lemma_insert_is_attach(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    ensures
        insert(doc, node, parent, child) == attach(adopt(doc, node), node, parent, insert_kids(doc, node, parent, child)),
{
}

/// The children of `parent` with `node` inserted as [`insert_kids`] does
/// it, as sequences.
pub proof fn lemma_kids_insert(kids1: Seq<NodeId>, node: NodeId, child: Option<NodeId>)
    requires
        kids1.no_duplicates(),
        !kids1.contains(node),
        child is Some ==> kids1.contains(child->Some_0),
    ensures
        insert_into(kids1, node, child).no_duplicates(),
        forall|y: NodeId| #[trigger] insert_into(kids1, node, child).contains(y) <==> (y == node || kids1.contains(y)),
{
    match child {
        None => {
            lemma_seq_insert(kids1, kids1.len() as int, node);
            assert(kids1.push(node) =~= kids1.insert(kids1.len() as int, node));
        },
        Some(c) => {
            lemma_index_of(kids1, c);
            lemma_seq_insert(kids1, index_of(kids1, c), node);
        },
    }
}

/// In a well-formed arena where `node` has no parent and `child` (if any)
/// has `parent` as its parent: `parent`'s children have no duplicates,
/// include `child` and not `node`.
pub proof fn lemma_listed(d: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        wf_with(d, paths),
        valid(d, node),
        valid(d, parent),
        d.nodes[node as int].parent is None,
        match child {
            None => true,
            Some(c) => valid(d, c) && d.nodes[c as int].parent == Some(parent),
        },
    ensures
        d.nodes[parent as int].children.no_duplicates(),
        !d.nodes[parent as int].children.contains(node),
        child is Some ==> d.nodes[parent as int].children.contains(child->Some_0),
{
    let kids1 = d.nodes[parent as int].children;
    if kids1.contains(node) {
        let j = choose|j: int| 0 <= j < kids1.len() && kids1[j] == node;
        assert(d.nodes[parent as int].children[j] == node);
    }
    if let Some(c) = child {
        assert(d.nodes[c as int].parent is Some);
    }
}

/// [`attach_requires`] from facts about the arena after step 7.1.
pub proof fn lemma_attach_requires_core(d1: Document, p1: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        wf_with(d1, p1),
        valid(d1, node),
        valid(d1, parent),
        d1.nodes[node as int].parent is None,
        !(d1.nodes[node as int].kind is Document),
        !(d1.nodes[node as int].kind is DocumentFragment),
        may_have_children(d1.nodes[parent as int].kind),
        !p1[parent as int].contains(node),
        match child {
            None => true,
            Some(c) => valid(d1, c) && d1.nodes[c as int].parent == Some(parent),
        },
    ensures
        attach_requires(d1, p1, node, parent, insert_into(d1.nodes[parent as int].children, node, child)),
{
    let kids1 = d1.nodes[parent as int].children;
    lemma_listed(d1, p1, node, parent, child);
    lemma_kids_insert(kids1, node, child);
}

/// The arguments of the [`attach`] in [`insert`] meet [`attach_requires`].
pub proof fn lemma_insert_attach_requires(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_requires(doc, node, parent, child),
        wf_with(doc, paths),
    ensures
        attach_requires(
            adopt(doc, node),
            if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths },
            node,
            parent,
            insert_kids(doc, node, parent, child),
        ),
{
    let d1 = adopt(doc, node);
    let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
    lemma_adopt(doc, paths, node, parent, child);
    assert(d1.nodes[node as int].kind == doc.nodes[node as int].kind);
    assert(d1.nodes[parent as int].kind == doc.nodes[parent as int].kind);
    lemma_attach_requires_core(d1, p1, node, parent, child);
}

/// DOM §4.2.3 "insert" keeps the arena well formed, with [`insert_paths`]
/// as the witness; paths that do not pass through `node` are unchanged.
pub proof fn lemma_insert_wf_with(doc: Document, paths: Seq<Seq<NodeId>>, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_requires(doc, node, parent, child),
        wf_with(doc, paths),
    ensures
        wf_with(insert(doc, node, parent, child), insert_paths(doc, paths, node, parent)),
        forall|x: int|
            0 <= x < doc.nodes.len() && !paths[x].contains(node) ==> #[trigger] insert_paths(doc, paths, node, parent)[x] == paths[x],
{
    let d1 = adopt(doc, node);
    let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
    let kids = insert_kids(doc, node, parent, child);
    lemma_adopt(doc, paths, node, parent, child);
    lemma_insert_is_attach(doc, node, parent, child);
    lemma_insert_attach_requires(doc, paths, node, parent, child);
    lemma_attach_wf_with(d1, p1, node, parent, kids);
    assert forall|x: int| 0 <= x < doc.nodes.len() && !paths[x].contains(node) implies #[trigger] insert_paths(doc, paths, node, parent)[x] == paths[x] by {
        assert(p1[x] == paths[x]);
    }
}

// ---------------------------------------------------------------------
// The theorems: creating nodes

/// A witness of a well-formed arena.
pub proof fn lemma_wf_witness(doc: Document) -> (paths: Seq<Seq<NodeId>>)
    requires
        wf(doc),
    ensures
        wf_with(doc, paths),
{
    choose|paths: Seq<Seq<NodeId>>| wf_with(doc, paths)
}

/// A fixed witness of a well-formed arena, as a spec function, so that
/// helper lemmas can name the same one.
pub open spec fn wf_witness(doc: Document) -> Seq<Seq<NodeId>> {
    choose|paths: Seq<Seq<NodeId>>| wf_with(doc, paths)
}

/// [`wf_witness`] is a witness.
pub proof fn lemma_wf_witness_is(doc: Document)
    requires
        wf(doc),
    ensures
        wf_with(doc, wf_witness(doc)),
{
}

/// DOM §4.5 "new Document()" is well formed.
pub proof fn theorem_new_document_wf(url: Seq<u32>)
    ensures
        wf(new_document(url)),
        new_document(url).nodes.len() == 1,
{
    let d = new_document(url);
    let paths = seq![seq![0usize]];
    assert(d.nodes[0].children =~= Seq::<NodeId>::empty());
    assert(wf_links(d));
    assert(wf_kinds(d));
    assert(paths[0] =~= seq![0usize]);
    assert(wf_paths(d, paths));
    lemma_wf_split(d, paths);
}

/// Part of [`theorem_create_node_wf`]: kinds.
pub proof fn lemma_create_node_kinds(doc: Document, k: NodeKind)
    requires
        wf(doc),
        creatable(doc, k),
        can_create(doc, 1),
    ensures
        wf_kinds(create_node(doc, k).0),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_node(doc, k).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    assert forall|i: int| 0 <= i < n implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Kinds.
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_template_contents is Some implies {
        let f = d.nodes[x].kind->Element_template_contents->Some_0;
        &&& f < n + 1
        &&& d.nodes[f as int].kind is DocumentFragment
        &&& d.nodes[f as int].kind->DocumentFragment_host == Some(x as NodeId)
    } by {
        assert(x < n);
        assert(doc.nodes[x].kind is Element);
        let f = doc.nodes[x].kind->Element_template_contents->Some_0;
        assert(d.nodes[f as int] == doc.nodes[f as int]);
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is DocumentFragment && d.nodes[x].kind->DocumentFragment_host is Some implies {
        let h = d.nodes[x].kind->DocumentFragment_host->Some_0;
        &&& h < n + 1
        &&& d.nodes[h as int].kind is Element
        &&& d.nodes[h as int].kind->Element_template_contents == Some(x as NodeId)
    } by {
        assert(x < n);
        assert(doc.nodes[x].kind is DocumentFragment);
        let h = doc.nodes[x].kind->DocumentFragment_host->Some_0;
        assert(d.nodes[h as int] == doc.nodes[h as int]);
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_form_owner is Some implies
        d.nodes[x].kind->Element_form_owner->Some_0 < n + 1 by {
        if x < n {
            assert(doc.nodes[x].kind is Element);
        }
    }
    assert forall|x: int| 0 < x < n + 1 implies !(#[trigger] d.nodes[x].kind is Document) by {
        if x < n {
            assert(!(doc.nodes[x].kind is Document));
        }
    }
    assert(wf_kinds(d));
}

/// Part of [`theorem_create_node_wf`]: links.
pub proof fn lemma_create_node_links(doc: Document, k: NodeKind)
    requires
        wf(doc),
        creatable(doc, k),
        can_create(doc, 1),
    ensures
        wf_links(create_node(doc, k).0),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_node(doc, k).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    assert forall|i: int| 0 <= i < n implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Links.
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).parent is Some implies {
        let r = d.nodes[x].parent->Some_0;
        &&& r < n + 1
        &&& d.nodes[r as int].children.contains(x as NodeId)
    } by {
        assert(doc.nodes[x].parent is Some);
        let r = doc.nodes[x].parent->Some_0;
        assert(d.nodes[r as int] == doc.nodes[r as int]);
    }
    assert forall|x: int, j: int| 0 <= x < n + 1 && 0 <= j < d.nodes[x].children.len() implies {
        let c = (#[trigger] d.nodes[x].children[j]);
        &&& c < n + 1
        &&& d.nodes[c as int].parent == Some(x as NodeId)
    } by {
        assert(x < n);
        assert(doc.nodes[x].children[j] == d.nodes[x].children[j]);
        let c = doc.nodes[x].children[j];
        assert(d.nodes[c as int] == doc.nodes[c as int]);
    }
    assert forall|x: int| 0 <= x < n + 1 implies (#[trigger] d.nodes[x]).children.no_duplicates() by {
        if x < n {
            assert(doc.nodes[x].children.no_duplicates());
        }
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).children.len() > 0 implies may_have_children(d.nodes[x].kind) by {
        assert(doc.nodes[x].children.len() > 0);
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is DocumentFragment implies d.nodes[x].parent is None by {
        if x < n {
            assert(doc.nodes[x].kind is DocumentFragment);
        }
    }
    assert(wf_links(d));
}

/// Part of [`theorem_create_node_wf`]: paths.
pub proof fn lemma_create_node_paths(doc: Document, k: NodeKind)
    requires
        wf(doc),
        creatable(doc, k),
        can_create(doc, 1),
    ensures
        wf_paths(create_node(doc, k).0, wf_witness(doc).push(seq![doc.nodes.len() as NodeId])),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_node(doc, k).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    assert forall|i: int| 0 <= i < n implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Paths.
    assert forall|x: int| 0 <= x < n + 1 implies #[trigger] q[x] == match d.nodes[x].parent {
        None => seq![x as NodeId],
        Some(r) => q[r as int].push(x as NodeId),
    } by {
        if x < n {
            assert(q[x] == paths[x]);
            assert(paths[x] == match doc.nodes[x].parent {
                None => seq![x as NodeId],
                Some(r) => paths[r as int].push(x as NodeId),
            });
            if let Some(r) = doc.nodes[x].parent {
                assert(r < n);
                assert(q[r as int] == paths[r as int]);
            }
        }
    }
    assert(wf_paths(d, q));
    lemma_wf_split(d, q);}

/// [`create_node`] keeps the arena well formed and adds one parentless,
/// childless node of kind `k` at the next id, changing no other record.
pub proof fn theorem_create_node_wf(doc: Document, k: NodeKind)
    requires
        wf(doc),
        creatable(doc, k),
        can_create(doc, 1),
    ensures
        wf(create_node(doc, k).0),
        create_node(doc, k).1 == doc.nodes.len(),
        create_node(doc, k).0.nodes.len() == doc.nodes.len() + 1,
        create_node(doc, k).0.nodes[doc.nodes.len() as int] == (Node { kind: k, parent: None, children: seq![], wrapper: None }),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] create_node(doc, k).0.nodes[i] == doc.nodes[i],
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let d = create_node(doc, k).0;
    let q = paths.push(seq![doc.nodes.len() as NodeId]);
    lemma_wf_split(doc, paths);
    lemma_create_node_kinds(doc, k);
    lemma_create_node_links(doc, k);
    lemma_create_node_paths(doc, k);
    let n = doc.nodes.len();
    assert forall|i: int| 0 <= i < n implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    lemma_wf_split(d, q);
}

/// Part of [`theorem_create_template_contents_wf`]: kinds.
pub proof fn lemma_ctc_kinds(doc: Document, t: NodeId)
    requires
        super::contract::create_template_contents_requires(doc, t),
        can_create(doc, 1),
    ensures
        wf_kinds(create_template_contents(doc, t).0),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_template_contents(doc, t).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    let tn = doc.nodes[t as int];
    assert(d.nodes[t as int].parent == tn.parent);
    assert(d.nodes[t as int].children == tn.children);
    assert(d.nodes[t as int].kind is Element);
    assert(d.nodes[t as int].kind->Element_form_owner == tn.kind->Element_form_owner);
    assert forall|i: int| 0 <= i < n && i != t implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Kinds.
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_template_contents is Some implies {
        let f = d.nodes[x].kind->Element_template_contents->Some_0;
        &&& f < n + 1
        &&& d.nodes[f as int].kind is DocumentFragment
        &&& d.nodes[f as int].kind->DocumentFragment_host == Some(x as NodeId)
    } by {
        if x != t {
            assert(x < n);
            assert(doc.nodes[x].kind is Element);
            let f = doc.nodes[x].kind->Element_template_contents->Some_0;
            assert(doc.nodes[f as int].kind is DocumentFragment);
            assert(f != t);
            assert(d.nodes[f as int] == doc.nodes[f as int]);
        }
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is DocumentFragment && d.nodes[x].kind->DocumentFragment_host is Some implies {
        let h = d.nodes[x].kind->DocumentFragment_host->Some_0;
        &&& h < n + 1
        &&& d.nodes[h as int].kind is Element
        &&& d.nodes[h as int].kind->Element_template_contents == Some(x as NodeId)
    } by {
        if x < n {
            assert(x != t);
            assert(doc.nodes[x].kind is DocumentFragment);
            let h = doc.nodes[x].kind->DocumentFragment_host->Some_0;
            assert(doc.nodes[h as int].kind->Element_template_contents == Some(x as NodeId));
            assert(h != t);
            assert(d.nodes[h as int] == doc.nodes[h as int]);
        }
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is Element && d.nodes[x].kind->Element_form_owner is Some implies
        d.nodes[x].kind->Element_form_owner->Some_0 < n + 1 by {
        if x < n {
            assert(doc.nodes[x].kind is Element);
        }
    }
    assert forall|x: int| 0 < x < n + 1 implies !(#[trigger] d.nodes[x].kind is Document) by {
        if x < n && x != t {
            assert(!(doc.nodes[x].kind is Document));
        }
    }
    assert(d.nodes[0].kind is Document) by {
        if t != 0 {
            assert(d.nodes[0] == doc.nodes[0]);
        }
    }
    assert(wf_kinds(d));
}

/// Part of [`theorem_create_template_contents_wf`]: links.
pub proof fn lemma_ctc_links(doc: Document, t: NodeId)
    requires
        super::contract::create_template_contents_requires(doc, t),
        can_create(doc, 1),
    ensures
        wf_links(create_template_contents(doc, t).0),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_template_contents(doc, t).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    let tn = doc.nodes[t as int];
    assert(d.nodes[t as int].parent == tn.parent);
    assert(d.nodes[t as int].children == tn.children);
    assert(d.nodes[t as int].kind is Element);
    assert(d.nodes[t as int].kind->Element_form_owner == tn.kind->Element_form_owner);
    assert forall|i: int| 0 <= i < n && i != t implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Links.
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).parent is Some implies {
        let r = d.nodes[x].parent->Some_0;
        &&& r < n + 1
        &&& d.nodes[r as int].children.contains(x as NodeId)
    } by {
        assert(doc.nodes[x].parent is Some);
        let r = doc.nodes[x].parent->Some_0;
        assert(d.nodes[r as int].children == doc.nodes[r as int].children);
    }
    assert forall|x: int, j: int| 0 <= x < n + 1 && 0 <= j < d.nodes[x].children.len() implies {
        let c = (#[trigger] d.nodes[x].children[j]);
        &&& c < n + 1
        &&& d.nodes[c as int].parent == Some(x as NodeId)
    } by {
        assert(x < n);
        assert(doc.nodes[x].children[j] == d.nodes[x].children[j]);
        let c = doc.nodes[x].children[j];
        assert(d.nodes[c as int].parent == doc.nodes[c as int].parent);
    }
    assert forall|x: int| 0 <= x < n + 1 implies (#[trigger] d.nodes[x]).children.no_duplicates() by {
        if x < n {
            assert(doc.nodes[x].children.no_duplicates());
        }
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).children.len() > 0 implies may_have_children(d.nodes[x].kind) by {
        assert(doc.nodes[x].children.len() > 0);
    }
    assert forall|x: int| 0 <= x < n + 1 && (#[trigger] d.nodes[x]).kind is DocumentFragment implies d.nodes[x].parent is None by {
        if x < n {
            assert(doc.nodes[x].kind is DocumentFragment);
        }
    }
    assert(d.nodes[0].parent is None);
    assert(wf_links(d));
}

/// Part of [`theorem_create_template_contents_wf`]: paths.
pub proof fn lemma_ctc_paths(doc: Document, t: NodeId)
    requires
        super::contract::create_template_contents_requires(doc, t),
        can_create(doc, 1),
    ensures
        wf_paths(create_template_contents(doc, t).0, wf_witness(doc).push(seq![doc.nodes.len() as NodeId])),
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let n = doc.nodes.len();
    let d = create_template_contents(doc, t).0;
    let id = n as NodeId;
    let q = paths.push(seq![id]);
    lemma_wf_split(doc, paths);
    let tn = doc.nodes[t as int];
    assert(d.nodes[t as int].parent == tn.parent);
    assert(d.nodes[t as int].children == tn.children);
    assert(d.nodes[t as int].kind is Element);
    assert(d.nodes[t as int].kind->Element_form_owner == tn.kind->Element_form_owner);
    assert forall|i: int| 0 <= i < n && i != t implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    // Paths.
    assert forall|x: int| 0 <= x < n + 1 implies #[trigger] q[x] == match d.nodes[x].parent {
        None => seq![x as NodeId],
        Some(r) => q[r as int].push(x as NodeId),
    } by {
        if x < n {
            assert(q[x] == paths[x]);
            assert(d.nodes[x].parent == doc.nodes[x].parent);
            assert(paths[x] == match doc.nodes[x].parent {
                None => seq![x as NodeId],
                Some(r) => paths[r as int].push(x as NodeId),
            });
            if let Some(r) = doc.nodes[x].parent {
                assert(r < n);
                assert(q[r as int] == paths[r as int]);
            }
        }
    }
    assert(wf_paths(d, q));
    lemma_wf_split(d, q);}

/// HTML §4.12.3 template contents keep the arena well formed: a new
/// parentless, childless fragment whose host is `t`, and `t`'s template
/// contents is it.
pub proof fn theorem_create_template_contents_wf(doc: Document, t: NodeId)
    requires
        super::contract::create_template_contents_requires(doc, t),
        can_create(doc, 1),
    ensures
        wf(create_template_contents(doc, t).0),
        create_template_contents(doc, t).1 == doc.nodes.len(),
        create_template_contents(doc, t).0.nodes.len() == doc.nodes.len() + 1,
        create_template_contents(doc, t).0.nodes[doc.nodes.len() as int] == (Node {
            kind: NodeKind::DocumentFragment { host: Some(t) },
            parent: None,
            children: seq![],
            wrapper: None,
        }),
        create_template_contents(doc, t).0.nodes[t as int].kind->Element_template_contents == Some(doc.nodes.len() as NodeId),
        forall|i: int| 0 <= i < doc.nodes.len() && i != t ==> #[trigger] create_template_contents(doc, t).0.nodes[i] == doc.nodes[i],
{
    let paths = wf_witness(doc);
    lemma_wf_witness_is(doc);
    let d = create_template_contents(doc, t).0;
    let q = paths.push(seq![doc.nodes.len() as NodeId]);
    lemma_wf_split(doc, paths);
    lemma_ctc_kinds(doc, t);
    lemma_ctc_links(doc, t);
    lemma_ctc_paths(doc, t);
    let n = doc.nodes.len();
    assert forall|i: int| 0 <= i < n && i != t implies #[trigger] d.nodes[i] == doc.nodes[i] by {}
    lemma_wf_split(d, q);
}

// ---------------------------------------------------------------------
// The theorems: mutation algorithms

/// DOM §4.2.3 "insert" keeps the arena well formed; `node`'s parent is
/// `parent` (step 7.2 or 7.3 put it in `parent`'s children), it is there
/// once, no kind changes, and a node other than `node` keeps its parent.
pub proof fn theorem_insert_wf(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_requires(doc, node, parent, child),
    ensures
        wf(insert(doc, node, parent, child)),
        insert(doc, node, parent, child).nodes.len() == doc.nodes.len(),
        insert(doc, node, parent, child).nodes[node as int].parent == Some(parent),
        insert(doc, node, parent, child).nodes[parent as int].children == insert_kids(doc, node, parent, child),
        insert(doc, node, parent, child).nodes[parent as int].children.no_duplicates(),
        forall|x: int| #![trigger insert(doc, node, parent, child).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& insert(doc, node, parent, child).nodes[x].kind == doc.nodes[x].kind
            &&& insert(doc, node, parent, child).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node ==> insert(doc, node, parent, child).nodes[x].parent == doc.nodes[x].parent)
        },
{
    let paths = lemma_wf_witness(doc);
    let d1 = adopt(doc, node);
    let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
    let kids = insert_kids(doc, node, parent, child);
    let e = insert(doc, node, parent, child);
    lemma_insert_wf_with(doc, paths, node, parent, child);
    lemma_insert_is_attach(doc, node, parent, child);
    lemma_insert_attach_requires(doc, paths, node, parent, child);
    lemma_adopt(doc, paths, node, parent, child);
    lemma_attach_nodes(d1, p1, node, parent, kids);
    assert forall|x: int| 0 <= x < doc.nodes.len() implies {
        &&& #[trigger] e.nodes[x].kind == doc.nodes[x].kind
        &&& e.nodes[x].wrapper == doc.nodes[x].wrapper
        &&& (x != node ==> e.nodes[x].parent == doc.nodes[x].parent)
    } by {
        assert(e.nodes[x] == attach(d1, node, parent, kids).nodes[x]);
        assert(d1.nodes[x].kind == doc.nodes[x].kind);
    }
}

/// DOM §4.2.3 "append" keeps the arena well formed and makes `node` the
/// last child of `parent`, after `parent`'s other children (those left
/// after step 7.1 removed `node` from its old parent).
pub proof fn theorem_append_wf(doc: Document, parent: NodeId, node: NodeId)
    requires
        insert_requires(doc, node, parent, None),
    ensures
        wf(append(doc, parent, node)),
        append(doc, parent, node).nodes.len() == doc.nodes.len(),
        super::spec::parent(append(doc, parent, node), node) == Some(parent),
        children(append(doc, parent, node), parent).len() == children(adopt(doc, node), parent).len() + 1,
        last_child(append(doc, parent, node), parent) == Some(node),
        forall|i: int| 0 <= i < children(adopt(doc, node), parent).len() ==>
            #[trigger] children(append(doc, parent, node), parent)[i] == children(adopt(doc, node), parent)[i],
{
    theorem_insert_wf(doc, node, parent, None);
}

/// DOM §4.2.3 "pre-insert" `node` before `child` keeps the arena well
/// formed, and puts `node` at `child`'s index (step 7.3), immediately
/// before `child`, so `child`'s previous sibling is `node`.
pub proof fn theorem_insert_before_wf(doc: Document, parent: NodeId, node: NodeId, child: NodeId)
    requires
        insert_requires(doc, node, parent, Some(child)),
    ensures
        wf(insert_before(doc, parent, node, child)),
        insert_before(doc, parent, node, child).nodes.len() == doc.nodes.len(),
        super::spec::parent(insert_before(doc, parent, node, child), node) == Some(parent),
        ({
            let kids1 = children(adopt(doc, node), parent);
            let i = index_of(kids1, child);
            let kids = children(insert_before(doc, parent, node, child), parent);
            &&& 0 <= i < kids1.len()
            &&& kids.len() == kids1.len() + 1
            &&& kids[i] == node
            &&& kids[i + 1] == child
        }),
        previous_sibling(insert_before(doc, parent, node, child), child) == Some(node),
{
    let paths = lemma_wf_witness(doc);
    theorem_insert_wf(doc, node, parent, Some(child));
    lemma_adopt(doc, paths, node, parent, Some(child));
    let d1 = adopt(doc, node);
    let p1 = if doc.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
    lemma_wf_split(d1, p1);
    let kids1 = children(d1, parent);
    assert(kids1.contains(child));
    lemma_index_of(kids1, child);
    let i = index_of(kids1, child);
    let e = insert_before(doc, parent, node, child);
    let kids = children(e, parent);
    lemma_insert_attach_requires(doc, paths, node, parent, Some(child));
    if kids1.contains(node) {
        let j = choose|j: int| 0 <= j < kids1.len() && kids1[j] == node;
        assert(d1.nodes[parent as int].children[j] == node);
    }
    lemma_seq_insert(kids1, i, node);
    assert(kids[i + 1] == kids1[i]);
    assert(e.nodes[child as int].parent == doc.nodes[child as int].parent);
    lemma_index_of_unique(kids, i + 1);
}

/// DOM §4.2.3 "remove" keeps the arena well formed: `node` has no parent
/// and its old parent's children no longer include it, one fewer.
pub proof fn theorem_remove_wf(doc: Document, node: NodeId)
    requires
        super::contract::remove_requires(doc, node),
    ensures
        wf(remove(doc, node)),
        super::spec::parent(remove(doc, node), node) is None,
        ({
            let p = doc.nodes[node as int].parent->Some_0;
            &&& !children(remove(doc, node), p).contains(node)
            &&& children(remove(doc, node), p).len() == children(doc, p).len() - 1
        }),
{
    let paths = lemma_wf_witness(doc);
    lemma_remove_wf_with(doc, paths, node);
    lemma_remove_nodes(doc, paths, node);
    let p = doc.nodes[node as int].parent->Some_0;
    let kids = doc.nodes[p as int].children;
    assert(kids.no_duplicates());
    lemma_seq_remove(kids, index_of(kids, node));
}

/// "remove" detaches and never deletes: it changes only `node`'s parent
/// (to none) and its old parent's children; the arena's length, every
/// kind and every wrapper are unchanged, so ids stay valid.
pub proof fn theorem_remove_keeps_record(doc: Document, node: NodeId)
    requires
        super::contract::remove_requires(doc, node),
    ensures
        remove(doc, node).nodes.len() == doc.nodes.len(),
        remove(doc, node).nodes[node as int].parent is None,
        remove(doc, node).nodes[node as int].children == doc.nodes[node as int].children,
        forall|x: int| #![trigger remove(doc, node).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& remove(doc, node).nodes[x].kind == doc.nodes[x].kind
            &&& remove(doc, node).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (x != node ==> remove(doc, node).nodes[x].parent == doc.nodes[x].parent)
            &&& (x != doc.nodes[node as int].parent->Some_0 ==> remove(doc, node).nodes[x].children == doc.nodes[x].children)
        },
{
    let paths = lemma_wf_witness(doc);
    lemma_remove_nodes(doc, paths, node);
}

// ---------------------------------------------------------------------
// The theorems: data, attributes, mode

/// Replacing a node's kind by one that agrees on everything [`wf_with`]
/// reads of kinds.
pub open spec fn same_shape(a: NodeKind, b: NodeKind) -> bool {
    &&& (a is Document <==> b is Document)
    &&& may_have_children(a) == may_have_children(b)
    &&& (a is DocumentFragment <==> b is DocumentFragment)
    &&& (a is DocumentFragment ==> a->DocumentFragment_host == b->DocumentFragment_host)
    &&& (a is Element <==> b is Element)
    &&& (a is Element ==> a->Element_template_contents == b->Element_template_contents
        && a->Element_form_owner == b->Element_form_owner)
}

/// The arena with node `x`'s kind replaced by `k`.
pub open spec fn set_kind(doc: Document, x: NodeId, k: NodeKind) -> Document {
    Document { nodes: doc.nodes.update(x as int, Node { kind: k, ..doc.nodes[x as int] }) }
}

/// [`set_kind`] with a kind of the same shape keeps the arena well formed,
/// with the same witness.
pub proof fn lemma_set_kind_wf(doc: Document, paths: Seq<Seq<NodeId>>, x: NodeId, k: NodeKind)
    requires
        wf_with(doc, paths),
        valid(doc, x),
        same_shape(doc.nodes[x as int].kind, k),
    ensures
        wf_with(set_kind(doc, x, k), paths),
{
    let n = doc.nodes.len();
    let d = set_kind(doc, x, k);
    lemma_wf_split(doc, paths);
    assert forall|i: int| 0 <= i < n implies (#[trigger] d.nodes[i]).parent == doc.nodes[i].parent
        && d.nodes[i].children == doc.nodes[i].children
        && same_shape(doc.nodes[i].kind, d.nodes[i].kind) by {}
    assert forall|i: int| 0 < i < n implies !(#[trigger] d.nodes[i].kind is Document) by {
        assert(!(doc.nodes[i].kind is Document));
    }
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).kind is Element && d.nodes[i].kind->Element_template_contents is Some implies {
        let f = d.nodes[i].kind->Element_template_contents->Some_0;
        &&& f < n
        &&& d.nodes[f as int].kind is DocumentFragment
        &&& d.nodes[f as int].kind->DocumentFragment_host == Some(i as NodeId)
    } by {
        assert(doc.nodes[i].kind is Element);
        let f = doc.nodes[i].kind->Element_template_contents->Some_0;
        assert(same_shape(doc.nodes[f as int].kind, d.nodes[f as int].kind));
    }
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).kind is DocumentFragment && d.nodes[i].kind->DocumentFragment_host is Some implies {
        let h = d.nodes[i].kind->DocumentFragment_host->Some_0;
        &&& h < n
        &&& d.nodes[h as int].kind is Element
        &&& d.nodes[h as int].kind->Element_template_contents == Some(i as NodeId)
    } by {
        assert(doc.nodes[i].kind is DocumentFragment);
        let h = doc.nodes[i].kind->DocumentFragment_host->Some_0;
        assert(same_shape(doc.nodes[h as int].kind, d.nodes[h as int].kind));
    }
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).kind is Element && d.nodes[i].kind->Element_form_owner is Some implies
        d.nodes[i].kind->Element_form_owner->Some_0 < n by {
        assert(doc.nodes[i].kind is Element);
    }
    assert(same_shape(doc.nodes[0].kind, d.nodes[0].kind));
    assert(wf_kinds(d));
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).parent is Some implies {
        let r = d.nodes[i].parent->Some_0;
        &&& r < n
        &&& d.nodes[r as int].children.contains(i as NodeId)
    } by {
        assert(doc.nodes[i].parent is Some);
        let r = doc.nodes[i].parent->Some_0;
        assert(d.nodes[r as int].children == doc.nodes[r as int].children);
    }
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < d.nodes[i].children.len() implies {
        let c = (#[trigger] d.nodes[i].children[j]);
        &&& c < n
        &&& d.nodes[c as int].parent == Some(i as NodeId)
    } by {
        assert(doc.nodes[i].children[j] == d.nodes[i].children[j]);
        let c = doc.nodes[i].children[j];
        assert(d.nodes[c as int].parent == doc.nodes[c as int].parent);
    }
    assert forall|i: int| 0 <= i < n implies (#[trigger] d.nodes[i]).children.no_duplicates() by {
        assert(doc.nodes[i].children.no_duplicates());
    }
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).children.len() > 0 implies may_have_children(d.nodes[i].kind) by {
        assert(doc.nodes[i].children.len() > 0);
    }
    assert forall|i: int| 0 <= i < n && (#[trigger] d.nodes[i]).kind is DocumentFragment implies d.nodes[i].parent is None by {
        assert(doc.nodes[i].kind is DocumentFragment);
    }
    assert(wf_links(d));
    assert forall|i: int| 0 <= i < n implies #[trigger] paths[i] == match d.nodes[i].parent {
        None => seq![i as NodeId],
        Some(r) => paths[r as int].push(i as NodeId),
    } by {
        assert(paths[i] == match doc.nodes[i].parent {
            None => seq![i as NodeId],
            Some(r) => paths[r as int].push(i as NodeId),
        });
    }
    assert(wf_paths(d, paths));
    lemma_wf_split(d, paths);
}

/// DOM §4.10 "replace data" at the end keeps the arena well formed, and
/// the node's data is its old data followed by `data`.
pub proof fn theorem_append_data_wf(doc: Document, n: NodeId, data: Seq<u32>)
    requires
        super::contract::append_data_requires(doc, n),
    ensures
        wf(append_data(doc, n, data)),
        append_data(doc, n, data).nodes[n as int].kind == (NodeKind::Text { data: doc.nodes[n as int].kind->Text_data + data }),
{
    let paths = lemma_wf_witness(doc);
    let k = append_data(doc, n, data).nodes[n as int].kind;
    assert(append_data(doc, n, data) == set_kind(doc, n, k));
    lemma_set_kind_wf(doc, paths, n, k);
}

/// DOM §4.9 "append an attribute" keeps the arena well formed, and the
/// element's attribute list is its old one followed by `attr`.
pub proof fn theorem_append_attribute_wf(doc: Document, e: NodeId, attr: Attr)
    requires
        super::contract::append_attribute_requires(doc, e),
    ensures
        wf(append_attribute(doc, e, attr)),
        append_attribute(doc, e, attr).nodes[e as int].kind is Element,
        append_attribute(doc, e, attr).nodes[e as int].kind->Element_attributes == doc.nodes[e as int].kind->Element_attributes.push(attr),
{
    let paths = lemma_wf_witness(doc);
    let k = append_attribute(doc, e, attr).nodes[e as int].kind;
    assert(append_attribute(doc, e, attr) == set_kind(doc, e, k));
    lemma_set_kind_wf(doc, paths, e, k);
}

/// Setting the document's mode keeps the arena well formed, and the mode
/// is `mode`.
pub proof fn theorem_set_mode_wf(doc: Document, mode: DocumentMode)
    requires
        wf(doc),
    ensures
        wf(set_mode(doc, mode)),
        set_mode(doc, mode).nodes[0].kind is Document,
        set_mode(doc, mode).nodes[0].kind->Document_mode == mode,
{
    let paths = lemma_wf_witness(doc);
    let k = set_mode(doc, mode).nodes[0].kind;
    assert(set_mode(doc, mode) == set_kind(doc, 0, k));
    lemma_set_kind_wf(doc, paths, 0, k);
}

/// The node limit is exactly [`max_nodes`]: the arena may grow by `k`
/// nodes if and only if it then still holds at most 4,000,000 (the bound
/// [`wf_with`] states), so creation is refused only where a new node
/// would break well-formedness.
pub proof fn lemma_limit_exact(doc: Document, k: nat)
    ensures
        can_create(doc, k) <==> doc.nodes.len() + k <= 4_000_000,
{
}

// ---------------------------------------------------------------------
// The theorems: moving all children

/// The arena after the first `k` children of `from` have moved to the end
/// of `to`'s children and the first `j` of them have `to` as their parent.
/// [`reparent_children_n`] after `k` steps is this with `j == k`
/// ([`lemma_reparent_n`]); the executable arena moves the whole list first
/// and then sets the parents, so it passes through `k == len`, `j < len`.
pub open spec fn reparent_partial(doc: Document, from: NodeId, to: NodeId, k: int, j: int) -> Document {
    let f = doc.nodes[from as int].children;
    let t = doc.nodes[to as int].children;
    Document {
        nodes: Seq::new(
            doc.nodes.len(),
            |i: int|
                {
                    let nd = doc.nodes[i];
                    if i == from {
                        Node { children: f.subrange(k, f.len() as int), ..nd }
                    } else if i == to {
                        Node { children: t + f.subrange(0, k), ..nd }
                    } else if f.subrange(0, j).contains(i as NodeId) {
                        Node { parent: Some(to), ..nd }
                    } else {
                        nd
                    }
                },
        ),
    }
}

/// What [`reparent_children_requires`] gives about `from`'s children: they
/// are distinct nodes whose parent is `from`, and neither `from` nor `to`
/// is one of them.
pub proof fn lemma_reparent_facts(doc: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(doc, from, to),
    ensures
        ({
            let f = doc.nodes[from as int].children;
            &&& f.no_duplicates()
            &&& !f.contains(from)
            &&& !f.contains(to)
            &&& forall|j: int| 0 <= j < f.len() ==> (#[trigger] f[j]) < doc.nodes.len() && doc.nodes[f[j] as int].parent == Some(from)
        }),
{
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
    let f = doc.nodes[from as int].children;
    assert forall|j: int| 0 <= j < f.len() implies (#[trigger] f[j]) < doc.nodes.len() && doc.nodes[f[j] as int].parent == Some(from) by {
        assert(doc.nodes[from as int].children[j] == f[j]);
    }
    if f.contains(from) {
        let j = choose|j: int| 0 <= j < f.len() && f[j] == from;
        assert(f[j] == from);
        lemma_parent_not_self(doc, paths, from);
    }
    if f.contains(to) {
        let j = choose|j: int| 0 <= j < f.len() && f[j] == to;
        assert(f[j] == to);
        assert(paths[to as int] == paths[from as int].push(to));
        lemma_path(doc, paths, from);
        assert(paths[to as int][paths[from as int].len() - 1] == from);
        lemma_ancestor_iff_path(doc, paths, from, to);
    }
}

/// [`reparent_partial`] with nothing moved is the arena itself.
pub proof fn lemma_reparent_zero(doc: Document, from: NodeId, to: NodeId)
    requires
        valid(doc, from),
        valid(doc, to),
        from != to,
    ensures
        reparent_partial(doc, from, to, 0, 0) == doc,
{
    let r = reparent_partial(doc, from, to, 0, 0);
    let f = doc.nodes[from as int].children;
    let t = doc.nodes[to as int].children;
    assert(f.subrange(0, f.len() as int) =~= f);
    assert(t + f.subrange(0, 0) =~= t);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies #[trigger] r.nodes[i] == doc.nodes[i] by {
        if f.subrange(0, 0).contains(i as NodeId) {
            let j = choose|j: int| 0 <= j < 0 && f.subrange(0, 0)[j] == i as NodeId;
        }
    }
    assert(r.nodes =~= doc.nodes);
}

/// The first child of `from` may be appended to `to`.
pub proof fn lemma_reparent_step_valid(d: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(d, from, to),
        d.nodes[from as int].children.len() >= 1,
    ensures
        insert_requires(d, d.nodes[from as int].children[0], to, None),
        d.nodes[d.nodes[from as int].children[0] as int].parent == Some(from),
{
    let paths = lemma_wf_witness(d);
    lemma_reparent_facts(d, from, to);
    let f = d.nodes[from as int].children;
    let c0 = f[0];
    assert(c0 < d.nodes.len());
    assert(d.nodes[c0 as int].parent == Some(from));
    lemma_ancestor_iff_path(d, paths, from, to);
    lemma_ancestor_iff_path(d, paths, c0, to);
    if paths[to as int].contains(c0) {
        lemma_path_prefix(d, paths, c0, to);
        assert(paths[c0 as int] == paths[from as int].push(c0));
        lemma_path(d, paths, from);
        assert(paths[c0 as int][paths[from as int].len() - 1] == from);
        assert(paths[c0 as int].contains(from));
    }
    assert(c0 != 0);
    assert(!(d.nodes[c0 as int].kind is DocumentFragment));
}

/// The records after appending the first child `c0` of `from` to `to`.
pub open spec fn reparent_one(d: Document, from: NodeId, to: NodeId) -> Seq<Node> {
    let f = d.nodes[from as int].children;
    let c0 = f[0];
    Seq::new(
        d.nodes.len(),
        |i: int|
            if i == c0 {
                Node { parent: Some(to), ..d.nodes[i] }
            } else if i == from {
                Node { children: f.remove(0), ..d.nodes[i] }
            } else if i == to {
                Node { children: d.nodes[to as int].children.push(c0), ..d.nodes[i] }
            } else {
                d.nodes[i]
            },
    )
}

/// Appending the first child of `from` to `to` gives [`reparent_one`].
pub proof fn lemma_reparent_step_records(d: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(d, from, to),
        d.nodes[from as int].children.len() >= 1,
    ensures
        append(d, to, d.nodes[from as int].children[0]).nodes == reparent_one(d, from, to),
{
    lemma_reparent_step_valid(d, from, to);
    let paths = lemma_wf_witness(d);
    lemma_reparent_facts(d, from, to);
    let f = d.nodes[from as int].children;
    let c0 = f[0];
    let d1 = adopt(d, c0);
    lemma_remove_nodes(d, paths, c0);
    lemma_index_of_unique(f, 0);
    let p1 = remove_paths(paths, c0);
    let kids = insert_kids(d, c0, to, None);
    lemma_insert_is_attach(d, c0, to, None);
    lemma_insert_attach_requires(d, paths, c0, to, None);
    lemma_attach_nodes(d1, p1, c0, to, kids);
    let e = append(d, to, c0);
    let r = reparent_one(d, from, to);
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] e.nodes[i] == r[i] by {}
    assert(e.nodes =~= r);
}

/// [`reparent_one`] is [`reparent_partial`] with one child moved.
pub proof fn lemma_reparent_one(d: Document, from: NodeId, to: NodeId)
    requires
        d.nodes.len() <= max_nodes(),
        valid(d, from),
        valid(d, to),
        from != to,
        d.nodes[from as int].children.len() >= 1,
        !d.nodes[from as int].children.contains(from),
        !d.nodes[from as int].children.contains(to),
    ensures
        reparent_one(d, from, to) == reparent_partial(d, from, to, 1, 1).nodes,
{
    let f = d.nodes[from as int].children;
    let t = d.nodes[to as int].children;
    let c0 = f[0];
    let e = reparent_one(d, from, to);
    let r = reparent_partial(d, from, to, 1, 1);
    assert(f.contains(c0));
    assert(f.remove(0) =~= f.subrange(1, f.len() as int));
    assert(t.push(c0) =~= t + f.subrange(0, 1));
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] e[i] == r.nodes[i] by {
        if f.subrange(0, 1).contains(i as NodeId) {
            let j = choose|j: int| 0 <= j < 1 && f.subrange(0, 1)[j] == i as NodeId;
            assert(i == c0);
        }
        if i == c0 {
            assert(f.subrange(0, 1)[0] == c0);
        }
    }
    assert(e =~= r.nodes);
}

/// The first step of [`reparent_children_n`] is a valid "append", and
/// moves the first child.
pub proof fn lemma_reparent_step(d: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(d, from, to),
        d.nodes[from as int].children.len() >= 1,
    ensures
        insert_requires(d, d.nodes[from as int].children[0], to, None),
        append(d, to, d.nodes[from as int].children[0]) == reparent_partial(d, from, to, 1, 1),
{
    lemma_reparent_step_valid(d, from, to);
    lemma_reparent_facts(d, from, to);
    lemma_reparent_step_records(d, from, to);
    lemma_reparent_one(d, from, to);
}

/// Moving one child and then `m` more is moving `m + 1`.
pub proof fn lemma_reparent_compose(d: Document, from: NodeId, to: NodeId, m: int)
    requires
        valid(d, from),
        valid(d, to),
        from != to,
        d.nodes[from as int].children.no_duplicates(),
        !d.nodes[from as int].children.contains(from),
        !d.nodes[from as int].children.contains(to),
        0 <= m,
        m + 1 <= d.nodes[from as int].children.len(),
    ensures
        reparent_partial(reparent_partial(d, from, to, 1, 1), from, to, m, m) == reparent_partial(d, from, to, m + 1, m + 1),
{
    let f = d.nodes[from as int].children;
    let t = d.nodes[to as int].children;
    let d1 = reparent_partial(d, from, to, 1, 1);
    let f1 = d1.nodes[from as int].children;
    let a = reparent_partial(d1, from, to, m, m);
    let b = reparent_partial(d, from, to, m + 1, m + 1);
    assert(f1 == f.subrange(1, f.len() as int));
    assert(f1.subrange(m, f1.len() as int) =~= f.subrange(m + 1, f.len() as int));
    assert(d1.nodes[to as int].children + f1.subrange(0, m) =~= t + f.subrange(0, m + 1));
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] a.nodes[i] == b.nodes[i] by {
        if i != from && i != to {
            let x = i as NodeId;
            let in1 = f.subrange(0, 1).contains(x);
            let inm = f1.subrange(0, m).contains(x);
            let inb = f.subrange(0, m + 1).contains(x);
            if in1 {
                let j = choose|j: int| 0 <= j < 1 && f.subrange(0, 1)[j] == x;
                assert(f.subrange(0, m + 1)[j] == x);
            }
            if inm {
                let j = choose|j: int| 0 <= j < m && f1.subrange(0, m)[j] == x;
                assert(f.subrange(0, m + 1)[j + 1] == x);
            }
            if inb {
                let fm = f.subrange(0, m + 1);
                let j = choose|j: int| 0 <= j < fm.len() && #[trigger] fm[j] == x;
                if j == 0 {
                    assert(f.subrange(0, 1)[0] == x);
                } else {
                    assert(f1.subrange(0, m)[j - 1] == x);
                }
            }
            assert(inb == (in1 || inm));
        }
    }
    assert(a.nodes =~= b.nodes);
}

/// [`reparent_children_n`] after `k` steps is [`reparent_partial`] with
/// `k` moved, and the arena stays well formed.
pub proof fn lemma_reparent_n(d: Document, from: NodeId, to: NodeId, k: nat)
    requires
        reparent_children_requires(d, from, to),
        k <= d.nodes[from as int].children.len(),
    ensures
        reparent_children_n(d, from, to, k) == reparent_partial(d, from, to, k as int, k as int),
        wf(reparent_partial(d, from, to, k as int, k as int)),
    decreases k,
{
    if k == 0 {
        lemma_reparent_zero(d, from, to);
    } else {
        let paths = lemma_wf_witness(d);
        let f = d.nodes[from as int].children;
        let c0 = f[0];
        lemma_reparent_facts(d, from, to);
        lemma_reparent_step(d, from, to);
        let d1 = append(d, to, c0);
        theorem_insert_wf(d, c0, to, None);
        // `from` is still not an inclusive ancestor of `to`.
        lemma_insert_wf_with(d, paths, c0, to, None);
        let q = insert_paths(d, paths, c0, to);
        lemma_ancestor_iff_path(d, paths, c0, to);
        lemma_ancestor_iff_path(d, paths, from, to);
        assert(q[to as int] == paths[to as int]);
        lemma_ancestor_iff_path(d1, q, from, to);
        assert(d1.nodes[from as int].kind == d.nodes[from as int].kind);
        assert(d1.nodes[to as int].kind == d.nodes[to as int].kind);
        assert(reparent_children_requires(d1, from, to));
        assert(d1.nodes[from as int].children == f.subrange(1, f.len() as int));
        lemma_reparent_n(d1, from, to, (k - 1) as nat);
        lemma_reparent_compose(d, from, to, k - 1);
    }
}

/// What [`reparent_partial`] with everything moved says.
pub proof fn lemma_reparent_full(doc: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(doc, from, to),
    ensures
        ({
            let f = doc.nodes[from as int].children;
            let r = reparent_partial(doc, from, to, f.len() as int, f.len() as int);
            &&& r.nodes.len() == doc.nodes.len()
            &&& children(r, to) == children(doc, to) + f
            &&& children(r, from).len() == 0
            &&& forall|j: int| 0 <= j < f.len() ==> super::spec::parent(r, #[trigger] f[j]) == Some(to)
            &&& forall|x: int| #![trigger r.nodes[x]] 0 <= x < doc.nodes.len() ==> {
                &&& r.nodes[x].kind == doc.nodes[x].kind
                &&& r.nodes[x].wrapper == doc.nodes[x].wrapper
                &&& (!f.contains(x as NodeId) ==> r.nodes[x].parent == doc.nodes[x].parent)
            }
        }),
{
    let f = doc.nodes[from as int].children;
    let len = f.len();
    lemma_reparent_facts(doc, from, to);
    let r = reparent_partial(doc, from, to, len as int, len as int);
    assert(f.subrange(0, len as int) =~= f);
    assert forall|j: int| 0 <= j < len implies super::spec::parent(r, #[trigger] f[j]) == Some(to) by {
        assert(f.subrange(0, len as int)[j] == f[j]);
        assert(f[j] != from);
        assert(f[j] != to);
        assert(f.subrange(0, len as int).contains(f[j]));
    }
    assert forall|x: int| 0 <= x < doc.nodes.len() implies {
        &&& (#[trigger] r.nodes[x]).kind == doc.nodes[x].kind
        &&& r.nodes[x].wrapper == doc.nodes[x].wrapper
        &&& (!f.contains(x as NodeId) ==> r.nodes[x].parent == doc.nodes[x].parent)
    } by {}
}

/// HTML §13.2.6.4.7 step 4.17, "take all of the child nodes of furthest
/// block and append them to" `to`, keeps the arena well formed and does
/// what it says: `to`'s children are its old ones followed by `from`'s, in
/// order; `from` has none; each moved child's parent is `to`; no kind
/// changes and nothing else's parent changes.
pub proof fn theorem_reparent_children_wf(doc: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(doc, from, to),
    ensures
        wf(reparent_children(doc, from, to)),
        reparent_children(doc, from, to).nodes.len() == doc.nodes.len(),
        children(reparent_children(doc, from, to), to) == children(doc, to) + children(doc, from),
        children(reparent_children(doc, from, to), from).len() == 0,
        forall|j: int| 0 <= j < children(doc, from).len() ==>
            super::spec::parent(reparent_children(doc, from, to), #[trigger] children(doc, from)[j]) == Some(to),
        forall|x: int| #![trigger reparent_children(doc, from, to).nodes[x]] 0 <= x < doc.nodes.len() ==> {
            &&& reparent_children(doc, from, to).nodes[x].kind == doc.nodes[x].kind
            &&& reparent_children(doc, from, to).nodes[x].wrapper == doc.nodes[x].wrapper
            &&& (!children(doc, from).contains(x as NodeId) ==> reparent_children(doc, from, to).nodes[x].parent == doc.nodes[x].parent)
        },
{
    let f = doc.nodes[from as int].children;
    lemma_reparent_n(doc, from, to, f.len());
    lemma_reparent_full(doc, from, to);
}

// ---------------------------------------------------------------------
// Ids are stable

/// `new` keeps every node of `old` (its length grows by exactly `created`)
/// and the kind of each, except possibly node `target` (-1 for none).
pub open spec fn ids_stable(old: Document, new: Document, created: nat, target: int) -> bool {
    &&& new.nodes.len() == old.nodes.len() + created
    &&& forall|i: int| #![trigger new.nodes[i]] 0 <= i < old.nodes.len() && i != target ==> new.nodes[i].kind == old.nodes[i].kind
}

/// [`theorem_ids_stable`] for [`create_node`].
pub proof fn lemma_ids_stable_create_node(doc: Document)
    requires
        wf(doc),
    ensures
        forall|k: NodeKind| creatable(doc, k) && can_create(doc, 1) ==> ids_stable(doc, (#[trigger] create_node(doc, k)).0, 1, -1),
{
    assert forall|k: NodeKind| creatable(doc, k) && can_create(doc, 1) implies ids_stable(doc, (#[trigger] create_node(doc, k)).0, 1, -1) by {
        theorem_create_node_wf(doc, k);
    }
}

/// [`theorem_ids_stable`] for [`create_template_contents`].
pub proof fn lemma_ids_stable_create_template_contents(doc: Document)
    requires
        wf(doc),
    ensures
        forall|t: NodeId| super::contract::create_template_contents_requires(doc, t) && can_create(doc, 1)
            ==> ids_stable(doc, (#[trigger] create_template_contents(doc, t)).0, 1, t as int),
{
    assert forall|t: NodeId| super::contract::create_template_contents_requires(doc, t) && can_create(doc, 1)
        implies ids_stable(doc, (#[trigger] create_template_contents(doc, t)).0, 1, t as int) by {
        theorem_create_template_contents_wf(doc, t);
    }
}

/// [`theorem_ids_stable`] for [`insert`].
pub proof fn lemma_ids_stable_insert(doc: Document)
    requires
        wf(doc),
    ensures
        forall|node: NodeId, parent: NodeId, child: Option<NodeId>| insert_requires(doc, node, parent, child)
            ==> ids_stable(doc, #[trigger] insert(doc, node, parent, child), 0, -1),
{
    assert forall|node: NodeId, parent: NodeId, child: Option<NodeId>| insert_requires(doc, node, parent, child)
        implies ids_stable(doc, #[trigger] insert(doc, node, parent, child), 0, -1) by {
        theorem_insert_wf(doc, node, parent, child);
    }
}

/// [`theorem_ids_stable`] for [`append`].
pub proof fn lemma_ids_stable_append(doc: Document)
    requires
        wf(doc),
    ensures
        forall|parent: NodeId, node: NodeId| insert_requires(doc, node, parent, None)
            ==> ids_stable(doc, #[trigger] append(doc, parent, node), 0, -1),
{
    assert forall|parent: NodeId, node: NodeId| insert_requires(doc, node, parent, None)
        implies ids_stable(doc, #[trigger] append(doc, parent, node), 0, -1) by {
        theorem_insert_wf(doc, node, parent, None);
    }
}

/// [`theorem_ids_stable`] for [`insert_before`].
pub proof fn lemma_ids_stable_insert_before(doc: Document)
    requires
        wf(doc),
    ensures
        forall|parent: NodeId, node: NodeId, child: NodeId| insert_requires(doc, node, parent, Some(child))
            ==> ids_stable(doc, #[trigger] insert_before(doc, parent, node, child), 0, -1),
{
    assert forall|parent: NodeId, node: NodeId, child: NodeId| insert_requires(doc, node, parent, Some(child))
        implies ids_stable(doc, #[trigger] insert_before(doc, parent, node, child), 0, -1) by {
        theorem_insert_wf(doc, node, parent, Some(child));
    }
}

/// [`theorem_ids_stable`] for [`remove`].
pub proof fn lemma_ids_stable_remove(doc: Document)
    requires
        wf(doc),
    ensures
        forall|node: NodeId| super::contract::remove_requires(doc, node) ==> ids_stable(doc, #[trigger] remove(doc, node), 0, -1),
{
    assert forall|node: NodeId| super::contract::remove_requires(doc, node) implies ids_stable(doc, #[trigger] remove(doc, node), 0, -1) by {
        theorem_remove_keeps_record(doc, node);
    }
}

/// [`theorem_ids_stable`] for [`reparent_children`].
pub proof fn lemma_ids_stable_reparent_children(doc: Document)
    requires
        wf(doc),
    ensures
        forall|from: NodeId, to: NodeId| reparent_children_requires(doc, from, to)
            ==> ids_stable(doc, #[trigger] reparent_children(doc, from, to), 0, -1),
{
    assert forall|from: NodeId, to: NodeId| reparent_children_requires(doc, from, to)
        implies ids_stable(doc, #[trigger] reparent_children(doc, from, to), 0, -1) by {
        theorem_reparent_children_wf(doc, from, to);
    }
}

/// [`theorem_ids_stable`] for [`append_data`].
pub proof fn lemma_ids_stable_append_data(doc: Document)
    requires
        wf(doc),
    ensures
        forall|n: NodeId, data: Seq<u32>| super::contract::append_data_requires(doc, n)
            ==> ids_stable(doc, #[trigger] append_data(doc, n, data), 0, n as int),
{

}

/// [`theorem_ids_stable`] for [`append_attribute`].
pub proof fn lemma_ids_stable_append_attribute(doc: Document)
    requires
        wf(doc),
    ensures
        forall|e: NodeId, attr: Attr| super::contract::append_attribute_requires(doc, e)
            ==> ids_stable(doc, #[trigger] append_attribute(doc, e, attr), 0, e as int),
{

}

/// [`theorem_ids_stable`] for [`set_mode`].
pub proof fn lemma_ids_stable_set_mode(doc: Document)
    requires
        wf(doc),
    ensures
        forall|mode: DocumentMode| ids_stable(doc, #[trigger] set_mode(doc, mode), 0, 0),
{

}

/// Ids are never reused and records never deleted: every operation keeps
/// the arena's length or grows it by exactly the nodes it creates, and
/// changes no existing node's kind except its own target's (the template
/// for [`create_template_contents`], the node for [`append_data`] and
/// [`append_attribute`], the document for [`set_mode`]).
pub proof fn theorem_ids_stable(doc: Document)
    requires
        wf(doc),
    ensures
        forall|k: NodeKind| creatable(doc, k) && can_create(doc, 1) ==> ids_stable(doc, (#[trigger] create_node(doc, k)).0, 1, -1),
        forall|t: NodeId| super::contract::create_template_contents_requires(doc, t) && can_create(doc, 1)
            ==> ids_stable(doc, (#[trigger] create_template_contents(doc, t)).0, 1, t as int),
        forall|node: NodeId, parent: NodeId, child: Option<NodeId>| insert_requires(doc, node, parent, child)
            ==> ids_stable(doc, #[trigger] insert(doc, node, parent, child), 0, -1),
        forall|parent: NodeId, node: NodeId| insert_requires(doc, node, parent, None)
            ==> ids_stable(doc, #[trigger] append(doc, parent, node), 0, -1),
        forall|parent: NodeId, node: NodeId, child: NodeId| insert_requires(doc, node, parent, Some(child))
            ==> ids_stable(doc, #[trigger] insert_before(doc, parent, node, child), 0, -1),
        forall|node: NodeId| super::contract::remove_requires(doc, node) ==> ids_stable(doc, #[trigger] remove(doc, node), 0, -1),
        forall|from: NodeId, to: NodeId| reparent_children_requires(doc, from, to)
            ==> ids_stable(doc, #[trigger] reparent_children(doc, from, to), 0, -1),
        forall|n: NodeId, data: Seq<u32>| super::contract::append_data_requires(doc, n)
            ==> ids_stable(doc, #[trigger] append_data(doc, n, data), 0, n as int),
        forall|e: NodeId, attr: Attr| super::contract::append_attribute_requires(doc, e)
            ==> ids_stable(doc, #[trigger] append_attribute(doc, e, attr), 0, e as int),
        forall|mode: DocumentMode| ids_stable(doc, #[trigger] set_mode(doc, mode), 0, 0),
{
    lemma_ids_stable_create_node(doc);
    lemma_ids_stable_create_template_contents(doc);
    lemma_ids_stable_insert(doc);
    lemma_ids_stable_append(doc);
    lemma_ids_stable_insert_before(doc);
    lemma_ids_stable_remove(doc);
    lemma_ids_stable_reparent_children(doc);
    lemma_ids_stable_append_data(doc);
    lemma_ids_stable_append_attribute(doc);
    lemma_ids_stable_set_mode(doc);
}

} // verus!
