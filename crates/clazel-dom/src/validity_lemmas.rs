//! Phase 7 item 7.13: the checks of DOM §4.2.3† "ensure pre-insertion
//! validity" and "replace", steps 5 and 6, enforce the children rules
//! ([`children_rules_hold`]) exactly.
//!
//! For a call whose node has no parent, and which passes steps 1 to 4:
//! it passes steps 5 and 6 if and only if the tree after the insertion
//! obeys the rules. [`theorem_pre_insert_children_rules`] and
//! [`theorem_replace_children_rules`] are the two theorems (listed in
//! `Cargo.toml`); everything else here is their machinery.
//!
//! The counts of the checks ([`count_tag`]) are bridged to the positions
//! the rules talk about ([`document_children_ok`]) by the `lemma_count_*`
//! lemmas; [`lemma_ok_insert_nodes`] and [`lemma_ok_insert_doctype`] say
//! when inserting a list of nodes in the middle of a document's children
//! keeps the rules.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Counts and positions

/// A count is positive exactly when some entry has the tag (and is not the
/// skipped node).
pub proof fn lemma_count_pos(doc: Document, s: Seq<NodeId>, t: NodeTag, skip: Option<NodeId>)
    ensures
        count_tag(doc, s, t, skip) > 0 <==> exists|j: int|
            #![trigger s[j]]
            0 <= j < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_count_pos(doc, d, t, skip);
        let last = s.last();
        if has_tag(doc.nodes[last as int].kind, t) && skip != Some(last) {
            assert(s[s.len() - 1] == last);
        } else {
            if exists|j: int| #![trigger s[j]] 0 <= j < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]) {
                let j = choose|j: int| #![trigger s[j]] 0 <= j < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]);
                assert(j < s.len() - 1);
                assert(d[j] == s[j]);
            }
        }
        if exists|j: int| #![trigger d[j]] 0 <= j < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]) {
            let j = choose|j: int| #![trigger d[j]] 0 <= j < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]);
            assert(s[j] == d[j]);
        }
    }
}

/// A count is at least 2 exactly when two entries have the tag (and are not
/// the skipped node).
pub proof fn lemma_count_two(doc: Document, s: Seq<NodeId>, t: NodeTag, skip: Option<NodeId>)
    ensures
        count_tag(doc, s, t, skip) >= 2 <==> exists|j: int, k: int|
            #![trigger s[j], s[k]]
            0 <= j < k < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]) && has_tag(doc.nodes[s[k] as int].kind, t)
                && skip != Some(s[k]),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_count_two(doc, d, t, skip);
        lemma_count_pos(doc, d, t, skip);
        let last = s.last();
        let lt = has_tag(doc.nodes[last as int].kind, t) && skip != Some(last);
        if lt {
            if count_tag(doc, d, t, skip) >= 1 {
                let j = choose|j: int| #![trigger d[j]] 0 <= j < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]);
                assert(s[j] == d[j]);
                assert(s[s.len() - 1] == last);
            }
        }
        if exists|j: int, k: int|
            #![trigger s[j], s[k]]
            0 <= j < k < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]) && has_tag(doc.nodes[s[k] as int].kind, t)
                && skip != Some(s[k]) {
            let (j, k) = choose|j: int, k: int|
                #![trigger s[j], s[k]]
                0 <= j < k < s.len() && has_tag(doc.nodes[s[j] as int].kind, t) && skip != Some(s[j]) && has_tag(doc.nodes[s[k] as int].kind, t)
                    && skip != Some(s[k]);
            if k == s.len() - 1 {
                assert(d[j] == s[j]);
                assert(0 <= j < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]));
            } else {
                assert(d[j] == s[j]);
                assert(d[k] == s[k]);
            }
        }
        if exists|j: int, k: int|
            #![trigger d[j], d[k]]
            0 <= j < k < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]) && has_tag(doc.nodes[d[k] as int].kind, t)
                && skip != Some(d[k]) {
            let (j, k) = choose|j: int, k: int|
                #![trigger d[j], d[k]]
                0 <= j < k < d.len() && has_tag(doc.nodes[d[j] as int].kind, t) && skip != Some(d[j]) && has_tag(doc.nodes[d[k] as int].kind, t)
                    && skip != Some(d[k]);
            assert(s[j] == d[j]);
            assert(s[k] == d[k]);
        }
    }
}

/// The count of a concatenation is the sum of the counts.
pub proof fn lemma_count_add(doc: Document, a: Seq<NodeId>, b: Seq<NodeId>, t: NodeTag, skip: Option<NodeId>)
    ensures
        count_tag(doc, a + b, t, skip) == count_tag(doc, a, t, skip) + count_tag(doc, b, t, skip),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_count_add(doc, a, b.drop_last(), t, skip);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

// ---------------------------------------------------------------------
// The rules and sub-sequences

/// A sub-sequence of a document's children (entries kept in order) obeys
/// the rules if the whole does.
pub proof fn lemma_ok_subseq(doc: Document, a: Seq<NodeId>, b: Seq<NodeId>, f: spec_fn(int) -> int)
    requires
        document_children_ok(doc, b),
        forall|j: int| 0 <= j < a.len() ==> 0 <= #[trigger] f(j) < b.len() && b[f(j)] == a[j],
        forall|j: int, k: int| 0 <= j < k < a.len() ==> #[trigger] f(j) < #[trigger] f(k),
    ensures
        document_children_ok(doc, a),
{
    assert forall|j: int| 0 <= j < a.len() implies !(doc.nodes[#[trigger] a[j] as int].kind is Text) by {
        assert(b[f(j)] == a[j]);
    }
    assert forall|j: int, k: int| 0 <= j < k < a.len() implies !(doc.nodes[#[trigger] a[j] as int].kind is Element
        && doc.nodes[#[trigger] a[k] as int].kind is Element) by {
        assert(b[f(j)] == a[j]);
        assert(b[f(k)] == a[k]);
        assert(f(j) < f(k));
    }
    assert forall|j: int, k: int| 0 <= j < k < a.len() implies !(doc.nodes[#[trigger] a[j] as int].kind is DocumentType
        && doc.nodes[#[trigger] a[k] as int].kind is DocumentType) by {
        assert(b[f(j)] == a[j]);
        assert(b[f(k)] == a[k]);
        assert(f(j) < f(k));
    }
    assert forall|j: int, k: int| 0 <= j < k < a.len() implies !(doc.nodes[#[trigger] a[j] as int].kind is Element
        && doc.nodes[#[trigger] a[k] as int].kind is DocumentType) by {
        assert(b[f(j)] == a[j]);
        assert(b[f(k)] == a[k]);
        assert(f(j) < f(k));
    }
}

/// Dropping the middle of `p + mid + s` keeps the rules.
pub proof fn lemma_ok_drop_mid(doc: Document, p: Seq<NodeId>, mid: Seq<NodeId>, s: Seq<NodeId>)
    requires
        document_children_ok(doc, p + mid + s),
    ensures
        document_children_ok(doc, p + s),
{
    let m = mid.len() as int;
    let pl = p.len() as int;
    lemma_ok_subseq(doc, p + s, p + mid + s, |j: int| if j < pl { j } else { j + m });
}

/// The entries of `p + ins + s` and of `p + s`, by position.
proof fn lemma_concat_index(p: Seq<NodeId>, ins: Seq<NodeId>, s: Seq<NodeId>)
    ensures
        (p + ins + s).len() == p.len() + ins.len() + s.len(),
        (p + s).len() == p.len() + s.len(),
        forall|a: int| 0 <= a < p.len() ==> (#[trigger] (p + ins + s)[a]) == p[a],
        forall|a: int| p.len() <= a < p.len() + ins.len() ==> (#[trigger] (p + ins + s)[a]) == ins[a - p.len()],
        forall|a: int| p.len() + ins.len() <= a < p.len() + ins.len() + s.len() ==> (#[trigger] (p + ins + s)[a]) == s[a - p.len() - ins.len()],
        forall|a: int| 0 <= a < p.len() ==> (#[trigger] (p + s)[a]) == p[a],
        forall|a: int| p.len() <= a < p.len() + s.len() ==> (#[trigger] (p + s)[a]) == s[a - p.len()],
{
}

/// Inserting `ins`, none of which is a doctype, between `p` and `s`, in a
/// document whose children `p + s` obey the rules: the result obeys them
/// exactly when `ins` has no `Text` and at most one element, and, if it has
/// an element, neither `p` nor `s` has one and `s` has no doctype.
#[verifier::rlimit(100)]
pub proof fn lemma_ok_insert_nodes(doc: Document, p: Seq<NodeId>, ins: Seq<NodeId>, s: Seq<NodeId>)
    requires
        document_children_ok(doc, p + s),
        forall|j: int| 0 <= j < ins.len() ==> !(doc.nodes[#[trigger] ins[j] as int].kind is DocumentType),
    ensures
        document_children_ok(doc, p + ins + s) <==> (count_tag(doc, ins, NodeTag::Text, None) == 0 && count_tag(doc, ins, NodeTag::Element, None) <= 1
            && (count_tag(doc, ins, NodeTag::Element, None) == 0 || (count_tag(doc, p + s, NodeTag::Element, None) == 0 && count_tag(
            doc,
            s,
            NodeTag::DocumentType,
            None,
        ) == 0))),
{
    let q = p + ins + s;
    let ps = p + s;
    let pl = p.len() as int;
    let il = ins.len() as int;
    lemma_concat_index(p, ins, s);
    lemma_count_pos(doc, ins, NodeTag::Text, None);
    lemma_count_pos(doc, ins, NodeTag::Element, None);
    lemma_count_two(doc, ins, NodeTag::Element, None);
    lemma_count_pos(doc, ps, NodeTag::Element, None);
    lemma_count_pos(doc, s, NodeTag::DocumentType, None);
    let tx = count_tag(doc, ins, NodeTag::Text, None);
    let el = count_tag(doc, ins, NodeTag::Element, None);
    let el_ps = count_tag(doc, ps, NodeTag::Element, None);
    let dt_s = count_tag(doc, s, NodeTag::DocumentType, None);
    if document_children_ok(doc, q) {
        if tx > 0 {
            let j = choose|j: int| #![trigger ins[j]] 0 <= j < ins.len() && doc.nodes[ins[j] as int].kind is Text;
            assert(q[pl + j] == ins[j]);
        }
        if el >= 2 {
            let (j, k) = choose|j: int, k: int|
                #![trigger ins[j], ins[k]]
                0 <= j < k < ins.len() && doc.nodes[ins[j] as int].kind is Element && doc.nodes[ins[k] as int].kind is Element;
            assert(q[pl + j] == ins[j]);
            assert(q[pl + k] == ins[k]);
        }
        if el > 0 {
            let j = choose|j: int| #![trigger ins[j]] 0 <= j < ins.len() && doc.nodes[ins[j] as int].kind is Element;
            assert(q[pl + j] == ins[j]);
            if el_ps > 0 {
                let m = choose|m: int| #![trigger ps[m]] 0 <= m < ps.len() && doc.nodes[ps[m] as int].kind is Element;
                if m < pl {
                    assert(q[m] == p[m]);
                    assert(ps[m] == p[m]);
                } else {
                    assert(q[m + il] == s[m - pl]);
                    assert(ps[m] == s[m - pl]);
                }
            }
            if dt_s > 0 {
                let m = choose|m: int| #![trigger s[m]] 0 <= m < s.len() && doc.nodes[s[m] as int].kind is DocumentType;
                assert(q[pl + il + m] == s[m]);
            }
        }
    }
    if tx == 0 && el <= 1 && (el == 0 || (el_ps == 0 && dt_s == 0)) {
        // No Text, and any element of ps would show up in the count.
        assert forall|a: int| 0 <= a < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Text) by {
            if a < pl {
                assert(ps[a] == p[a]);
            } else if a < pl + il {
                assert(q[a] == ins[a - pl]);
            } else {
                assert(ps[a - il] == s[a - pl - il]);
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Element
            && doc.nodes[#[trigger] q[b] as int].kind is Element) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b < pl + il {
                assert(q[b] == ins[b - pl]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else {
                    assert(q[a] == ins[a - pl]);
                }
            } else {
                assert(q[b] == s[b - pl - il]);
                assert(ps[b - il] == s[b - pl - il]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a < pl + il {
                    assert(q[a] == ins[a - pl]);
                } else {
                    assert(ps[a - il] == s[a - pl - il]);
                }
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is DocumentType
            && doc.nodes[#[trigger] q[b] as int].kind is DocumentType) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b < pl + il {
                assert(q[b] == ins[b - pl]);
            } else {
                assert(q[b] == s[b - pl - il]);
                assert(ps[b - il] == s[b - pl - il]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a < pl + il {
                    assert(q[a] == ins[a - pl]);
                } else {
                    assert(ps[a - il] == s[a - pl - il]);
                }
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Element
            && doc.nodes[#[trigger] q[b] as int].kind is DocumentType) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b < pl + il {
                assert(q[b] == ins[b - pl]);
            } else {
                assert(q[b] == s[b - pl - il]);
                assert(ps[b - il] == s[b - pl - il]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a < pl + il {
                    assert(q[a] == ins[a - pl]);
                } else {
                    assert(ps[a - il] == s[a - pl - il]);
                }
            }
        }
    }
}

/// Inserting the doctype `d` between `p` and `s`, in a document whose
/// children `p + s` obey the rules: the result obeys them exactly when
/// `p + s` has no doctype and `p` has no element.
#[verifier::rlimit(100)]
pub proof fn lemma_ok_insert_doctype(doc: Document, p: Seq<NodeId>, d: NodeId, s: Seq<NodeId>)
    requires
        document_children_ok(doc, p + s),
        doc.nodes[d as int].kind is DocumentType,
    ensures
        document_children_ok(doc, p + seq![d] + s) <==> (count_tag(doc, p + s, NodeTag::DocumentType, None) == 0 && count_tag(
            doc,
            p,
            NodeTag::Element,
            None,
        ) == 0),
{
    let q = p + seq![d] + s;
    let ps = p + s;
    let pl = p.len() as int;
    lemma_concat_index(p, seq![d], s);
    lemma_count_pos(doc, ps, NodeTag::DocumentType, None);
    lemma_count_pos(doc, p, NodeTag::Element, None);
    let dt_ps = count_tag(doc, ps, NodeTag::DocumentType, None);
    let el_p = count_tag(doc, p, NodeTag::Element, None);
    assert(q[pl] == d);
    if document_children_ok(doc, q) {
        if dt_ps > 0 {
            let m = choose|m: int| #![trigger ps[m]] 0 <= m < ps.len() && doc.nodes[ps[m] as int].kind is DocumentType;
            if m < pl {
                assert(q[m] == p[m]);
                assert(ps[m] == p[m]);
            } else {
                assert(q[m + 1] == s[m - pl]);
                assert(ps[m] == s[m - pl]);
            }
        }
        if el_p > 0 {
            let m = choose|m: int| #![trigger p[m]] 0 <= m < p.len() && doc.nodes[p[m] as int].kind is Element;
            assert(q[m] == p[m]);
        }
    }
    if dt_ps == 0 && el_p == 0 {
        assert forall|a: int| 0 <= a < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Text) by {
            if a < pl {
                assert(ps[a] == p[a]);
            } else if a == pl {
            } else {
                assert(ps[a - 1] == s[a - pl - 1]);
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Element
            && doc.nodes[#[trigger] q[b] as int].kind is Element) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b == pl {
            } else {
                assert(q[b] == s[b - pl - 1]);
                assert(ps[b - 1] == s[b - pl - 1]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a == pl {
                } else {
                    assert(ps[a - 1] == s[a - pl - 1]);
                }
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is DocumentType
            && doc.nodes[#[trigger] q[b] as int].kind is DocumentType) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b == pl {
                assert(ps[a] == p[a]);
            } else {
                assert(q[b] == s[b - pl - 1]);
                assert(ps[b - 1] == s[b - pl - 1]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a == pl {
                } else {
                    assert(ps[a - 1] == s[a - pl - 1]);
                }
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < q.len() implies !(doc.nodes[#[trigger] q[a] as int].kind is Element
            && doc.nodes[#[trigger] q[b] as int].kind is DocumentType) by {
            if b < pl {
                assert(ps[a] == p[a]);
                assert(ps[b] == p[b]);
            } else if b == pl {
                assert(ps[a] == p[a]);
            } else {
                assert(q[b] == s[b - pl - 1]);
                assert(ps[b - 1] == s[b - pl - 1]);
                if a < pl {
                    assert(ps[a] == p[a]);
                } else if a == pl {
                } else {
                    assert(ps[a - 1] == s[a - pl - 1]);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The checks of step 6, by the split they are about

/// Skipping a node that is not in the sequence changes no count.
pub proof fn lemma_count_skip_absent(doc: Document, s: Seq<NodeId>, t: NodeTag, c: NodeId)
    requires
        !s.contains(c),
    ensures
        count_tag(doc, s, t, Some(c)) == count_tag(doc, s, t, None),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(s[s.len() - 1] == s.last());
        assert forall|j: int| 0 <= j < d.len() implies d[j] != c by {
            assert(d[j] == s[j]);
        }
        assert(!d.contains(c));
        lemma_count_skip_absent(doc, d, t, c);
        assert(s.last() != c);
    }
}

/// The count of a one-element sequence.
pub proof fn lemma_count_single(doc: Document, c: NodeId, t: NodeTag, skip: Option<NodeId>)
    ensures
        count_tag(doc, seq![c], t, skip) == if has_tag(doc.nodes[c as int].kind, t) && skip != Some(c) {
            1nat
        } else {
            0nat
        },
{
    assert(seq![c].drop_last() =~= Seq::<NodeId>::empty());
    assert(seq![c].last() == c);
    assert(count_tag(doc, Seq::<NodeId>::empty(), t, skip) == 0);
}

/// Skipping `c` in `p + [c] + s`, which has `c` only in the middle, counts
/// what `p` and `s` have.
pub proof fn lemma_count_skip_split(doc: Document, p: Seq<NodeId>, c: NodeId, s: Seq<NodeId>, t: NodeTag)
    requires
        !p.contains(c),
        !s.contains(c),
    ensures
        count_tag(doc, p + seq![c] + s, t, Some(c)) == count_tag(doc, p, t, None) + count_tag(doc, s, t, None),
{
    lemma_count_add(doc, p + seq![c], s, t, Some(c));
    lemma_count_add(doc, p, seq![c], t, Some(c));
    lemma_count_single(doc, c, t, Some(c));
    lemma_count_skip_absent(doc, p, t, c);
    lemma_count_skip_absent(doc, s, t, c);
}

/// The nodes `node` contributes to its new parent's children: a
/// fragment's children, or the node itself.
pub open spec fn inserted_nodes(doc: Document, node: NodeId) -> Seq<NodeId> {
    if doc.nodes[node as int].kind is DocumentFragment {
        doc.nodes[node as int].children
    } else {
        seq![node]
    }
}

/// The statements of step 6, switched on the interface `node` implements
/// (both "ensure pre-insertion validity" and "replace"), in terms of the
/// children `p` before and `s` after the place the nodes go in: "parent has
/// an element child" is a count over `p + s`, "a doctype is following
/// child" a count over `s`, "an element is preceding child" one over `p`.
pub open spec fn rules_violation(doc: Document, node: NodeId, p: Seq<NodeId>, s: Seq<NodeId>) -> bool {
    match doc.nodes[node as int].kind {
        NodeKind::DocumentFragment { .. } => {
            let el = count_tag(doc, doc.nodes[node as int].children, NodeTag::Element, None);
            let tx = count_tag(doc, doc.nodes[node as int].children, NodeTag::Text, None);
            el > 1 || tx > 0 || (el == 1 && (count_tag(doc, p + s, NodeTag::Element, None) > 0 || count_tag(doc, s, NodeTag::DocumentType, None) > 0))
        },
        NodeKind::Element { .. } => count_tag(doc, p + s, NodeTag::Element, None) > 0 || count_tag(doc, s, NodeTag::DocumentType, None) > 0,
        NodeKind::DocumentType { .. } => count_tag(doc, p + s, NodeTag::DocumentType, None) > 0 || count_tag(doc, p, NodeTag::Element, None) > 0,
        _ => false,
    }
}

/// Where "ensure pre-insertion validity" splits `parent`'s children: before
/// `child`, or at the end.
pub open spec fn split_index(kids: Seq<NodeId>, child: Option<NodeId>) -> int {
    match child {
        Some(c) => index_of(kids, c),
        None => kids.len() as int,
    }
}

/// Step 6 of "ensure pre-insertion validity" is [`rules_violation`] with
/// the children split at `child`.
pub proof fn lemma_pre_insert_violation(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        wf(doc),
        valid(doc, node),
        valid(doc, parent),
        match child {
            None => true,
            Some(c) => valid(doc, c) && doc.nodes[c as int].parent == Some(parent),
        },
    ensures
        ({
            let kids = children(doc, parent);
            let k = split_index(kids, child);
            &&& 0 <= k <= kids.len()
            &&& kids.subrange(0, k) + kids.subrange(k, kids.len() as int) == kids
            &&& pre_insert_document_violation(doc, node, parent, child) == rules_violation(
                doc,
                node,
                kids.subrange(0, k),
                kids.subrange(k, kids.len() as int),
            )
        }),
{
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    if let Some(c) = child {
        assert(kids.contains(c));
        lemma_index_of(kids, c);
    }
    let p = kids.subrange(0, k);
    let s = kids.subrange(k, kids.len() as int);
    assert(p + s =~= kids);
    lemma_count_add(doc, p, s, NodeTag::Element, None);
    lemma_count_add(doc, p, s, NodeTag::DocumentType, None);
    if let Some(c) = child {
        // s is child, then the siblings after it.
        let after_s = kids.subrange(k + 1, kids.len() as int);
        assert(s =~= seq![c] + after_s);
        lemma_count_add(doc, seq![c], after_s, NodeTag::DocumentType, None);
        lemma_count_single(doc, c, NodeTag::DocumentType, None);
    } else {
        assert(s =~= Seq::<NodeId>::empty());
    }
    assert(count_tag(doc, Seq::<NodeId>::empty(), NodeTag::DocumentType, None) == 0);
}

/// Step 6 of "replace" is [`rules_violation`] with the children split at
/// `child`, which is left out.
pub proof fn lemma_replace_violation(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        wf(doc),
        valid(doc, node),
        valid(doc, parent),
        valid(doc, child),
        doc.nodes[child as int].parent == Some(parent),
    ensures
        ({
            let kids = children(doc, parent);
            let i = index_of(kids, child);
            &&& 0 <= i < kids.len()
            &&& kids.subrange(0, i) + seq![child] + kids.subrange(i + 1, kids.len() as int) == kids
            &&& replace_document_violation(doc, child, node, parent) == rules_violation(
                doc,
                node,
                kids.subrange(0, i),
                kids.subrange(i + 1, kids.len() as int),
            )
        }),
{
    let kids = children(doc, parent);
    assert(kids.contains(child));
    lemma_index_of(kids, child);
    let i = index_of(kids, child);
    let p = kids.subrange(0, i);
    let s = kids.subrange(i + 1, kids.len() as int);
    assert(p + seq![child] + s =~= kids);
    assert(kids.no_duplicates());
    // `child` is neither in `p` nor in `s`.
    assert forall|j: int| 0 <= j < p.len() implies p[j] != child by {
        assert(p[j] == kids[j]);
        assert(kids[i] == child);
    }
    assert forall|j: int| 0 <= j < s.len() implies s[j] != child by {
        assert(s[j] == kids[i + 1 + j]);
        assert(kids[i] == child);
    }
    assert(!p.contains(child));
    assert(!s.contains(child));
    lemma_count_skip_split(doc, p, child, s, NodeTag::Element);
    lemma_count_skip_split(doc, p, child, s, NodeTag::DocumentType);
    lemma_count_add(doc, p, s, NodeTag::Element, None);
    lemma_count_add(doc, p, s, NodeTag::DocumentType, None);
}

/// A node `node` (not a document) inserted between `p` and `s`, in a
/// document whose children `p + s` obey the rules, and whose fragments'
/// children are not doctypes: the children afterwards obey the rules
/// exactly when `node` is not a `Text` node and [`rules_violation`] does
/// not hold.
pub proof fn lemma_ok_insert_node(doc: Document, node: NodeId, p: Seq<NodeId>, s: Seq<NodeId>)
    requires
        document_children_ok(doc, p + s),
        !(doc.nodes[node as int].kind is Document),
        doc.nodes[node as int].kind is DocumentFragment ==> forall|j: int|
            0 <= j < doc.nodes[node as int].children.len() ==> !(doc.nodes[#[trigger] doc.nodes[node as int].children[j] as int].kind is DocumentType),
    ensures
        document_children_ok(doc, p + inserted_nodes(doc, node) + s) <==> (!(doc.nodes[node as int].kind is Text) && !rules_violation(
            doc,
            node,
            p,
            s,
        )),
{
    let k = doc.nodes[node as int].kind;
    let ins = inserted_nodes(doc, node);
    if k is DocumentType {
        lemma_ok_insert_doctype(doc, p, node, s);
    } else {
        if !(k is DocumentFragment) {
            assert forall|j: int| 0 <= j < ins.len() implies !(doc.nodes[#[trigger] ins[j] as int].kind is DocumentType) by {
                assert(ins[j] == node);
            }
        }
        lemma_ok_insert_nodes(doc, p, ins, s);
        lemma_count_add(doc, p, s, NodeTag::Element, None);
        if !(k is DocumentFragment) {
            lemma_count_single(doc, node, NodeTag::Element, None);
            lemma_count_single(doc, node, NodeTag::Text, None);
        }
    }
}

// ---------------------------------------------------------------------
// The rules on the whole tree

/// Only kinds matter to the rules on a sequence.
pub proof fn lemma_ok_kinds(doc: Document, d2: Document, kids: Seq<NodeId>)
    requires
        d2.nodes.len() >= doc.nodes.len(),
        forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind,
        forall|j: int| 0 <= j < kids.len() ==> (#[trigger] kids[j]) < doc.nodes.len(),
        document_children_ok(doc, kids),
    ensures
        document_children_ok(d2, kids),
{
    assert forall|j: int| 0 <= j < kids.len() implies !(d2.nodes[#[trigger] kids[j] as int].kind is Text) by {
        assert(d2.nodes[kids[j] as int].kind == doc.nodes[kids[j] as int].kind);
    }
    assert forall|j: int, k: int| 0 <= j < k < kids.len() implies !(d2.nodes[#[trigger] kids[j] as int].kind is Element
        && d2.nodes[#[trigger] kids[k] as int].kind is Element) by {
        assert(d2.nodes[kids[j] as int].kind == doc.nodes[kids[j] as int].kind);
        assert(d2.nodes[kids[k] as int].kind == doc.nodes[kids[k] as int].kind);
    }
    assert forall|j: int, k: int| 0 <= j < k < kids.len() implies !(d2.nodes[#[trigger] kids[j] as int].kind is DocumentType
        && d2.nodes[#[trigger] kids[k] as int].kind is DocumentType) by {
        assert(d2.nodes[kids[j] as int].kind == doc.nodes[kids[j] as int].kind);
        assert(d2.nodes[kids[k] as int].kind == doc.nodes[kids[k] as int].kind);
    }
    assert forall|j: int, k: int| 0 <= j < k < kids.len() implies !(d2.nodes[#[trigger] kids[j] as int].kind is Element
        && d2.nodes[#[trigger] kids[k] as int].kind is DocumentType) by {
        assert(d2.nodes[kids[j] as int].kind == doc.nodes[kids[j] as int].kind);
        assert(d2.nodes[kids[k] as int].kind == doc.nodes[kids[k] as int].kind);
    }
}

/// The rules hold in `d2`, an arena of the same nodes and kinds as `doc`
/// (where they hold) in which only `parent`'s children, now `q`, changed,
/// except that some node may have lost all its children, exactly when
/// `q` obeys them: the document rules if `parent` is the document, and no
/// doctype otherwise.
pub proof fn lemma_rules_shape(doc: Document, d2: Document, parent: NodeId, q: Seq<NodeId>)
    requires
        wf(doc),
        wf(d2),
        children_rules_hold(doc),
        valid(doc, parent),
        d2.nodes.len() == doc.nodes.len(),
        forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind,
        d2.nodes[parent as int].children == q,
        forall|x: int|
            0 <= x < doc.nodes.len() && x != parent ==> (#[trigger] d2.nodes[x]).children == doc.nodes[x].children || d2.nodes[x].children.len() == 0,
    ensures
        children_rules_hold(d2) <==> (if doc.nodes[parent as int].kind is Document {
            document_children_ok(doc, q)
        } else {
            forall|j: int| 0 <= j < q.len() ==> !(doc.nodes[#[trigger] q[j] as int].kind is DocumentType)
        }),
{
    let n = doc.nodes.len();
    let paths = lemma_wf_witness(doc);
    let paths2 = lemma_wf_witness(d2);
    lemma_wf_split(doc, paths);
    lemma_wf_split(d2, paths2);
    assert(doc.nodes[0].kind is Document);
    assert forall|i: int| 0 < i < n implies !((#[trigger] doc.nodes[i]).kind is Document) by {}
    // Every child in either arena is a node of the arena.
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < d2.nodes[i].children.len() implies (#[trigger] d2.nodes[i].children[j]) < n by {}
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < doc.nodes[i].children.len() implies (#[trigger] doc.nodes[i].children[j]) < n by {}
    assert forall|j: int| 0 <= j < q.len() implies (#[trigger] q[j]) < n by {
        assert(d2.nodes[parent as int].children[j] == q[j]);
    }
    if children_rules_hold(d2) {
        if doc.nodes[parent as int].kind is Document {
            assert(parent == 0);
            assert(document_children_ok(d2, q));
            lemma_ok_kinds(d2, doc, q);
        } else {
            assert forall|j: int| 0 <= j < q.len() implies !(doc.nodes[#[trigger] q[j] as int].kind is DocumentType) by {
                assert(!(d2.nodes[parent as int].kind is Document));
                assert(d2.nodes[parent as int].children[j] == q[j]);
                assert(d2.nodes[q[j] as int].kind == doc.nodes[q[j] as int].kind);
            }
        }
    }
    let rule = if doc.nodes[parent as int].kind is Document {
        document_children_ok(doc, q)
    } else {
        forall|j: int| 0 <= j < q.len() ==> !(doc.nodes[#[trigger] q[j] as int].kind is DocumentType)
    };
    if rule {
        assert forall|p2: int, j: int|
            0 <= p2 < d2.nodes.len() && !(d2.nodes[p2].kind is Document) && 0 <= j < d2.nodes[p2].children.len() implies !(d2.nodes[#[trigger] d2.nodes[p2].children[j] as int].kind is DocumentType) by {
            let c = d2.nodes[p2].children[j];
            assert(d2.nodes[c as int].kind == doc.nodes[c as int].kind);
            assert(!(doc.nodes[p2].kind is Document));
            if p2 == parent as int {
                assert(q[j] == c);
            } else {
                assert(d2.nodes[p2].children == doc.nodes[p2].children);
                assert(doc.nodes[p2].children[j] == c);
            }
        }
        if parent == 0 {
            lemma_ok_kinds(doc, d2, q);
        } else {
            assert(!(doc.nodes[parent as int].kind is Document));
            if d2.nodes[0].children == doc.nodes[0].children {
                lemma_ok_kinds(doc, d2, doc.nodes[0].children);
            } else {
                assert(d2.nodes[0].children.len() == 0);
                assert(document_children_ok(d2, d2.nodes[0].children));
            }
        }
    }
}

// ---------------------------------------------------------------------
// What the insertion does to the children

/// What [`lemma_insert_any_shape`] says, for a call with a split index.
pub open spec fn insert_shape(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    let d2 = insert_any(doc, node, parent, child);
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    &&& wf(d2)
    &&& d2.nodes.len() == doc.nodes.len()
    &&& forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind
    &&& 0 <= k <= kids.len()
    &&& d2.nodes[parent as int].children == kids.subrange(0, k) + inserted_nodes(doc, node) + kids.subrange(k, kids.len() as int)
    &&& forall|x: int|
        0 <= x < doc.nodes.len() && x != parent ==> (#[trigger] d2.nodes[x]).children == doc.nodes[x].children || d2.nodes[x].children.len() == 0
}

/// [`lemma_insert_any_shape`] for a fragment.
#[verifier::rlimit(100)]
proof fn lemma_insert_any_shape_frag(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        doc.nodes[node as int].kind is DocumentFragment,
    ensures
        insert_shape(doc, node, parent, child),
{
    theorem_insert_any_wf(doc, node, parent, child);
    let d2 = insert_any(doc, node, parent, child);
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    if let Some(c) = child {
        let paths = lemma_wf_witness(doc);
        lemma_wf_split(doc, paths);
        assert(kids.contains(c));
        lemma_index_of(kids, c);
    }
    lemma_insert_fragment(doc, node, parent, child);
    assert(d2.nodes == fragment_inserted(doc, node, parent, child));
    assert forall|x: int| 0 <= x < doc.nodes.len() && x != parent implies (#[trigger] d2.nodes[x]).children == doc.nodes[x].children
        || d2.nodes[x].children.len() == 0 by {
        assert(d2.nodes[x] == fragment_inserted(doc, node, parent, child)[x]);
    }
    match child {
        None => {
            assert(kids.subrange(0, k) =~= kids);
            assert(kids.subrange(k, kids.len() as int) =~= Seq::<NodeId>::empty());
            assert(kids + doc.nodes[node as int].children + Seq::<NodeId>::empty() =~= kids + doc.nodes[node as int].children);
        },
        Some(c) => {},
    }
}

/// [`lemma_insert_any_shape`] for a node that is not a fragment.
#[verifier::rlimit(100)]
proof fn lemma_insert_any_shape_node(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        !(doc.nodes[node as int].kind is DocumentFragment),
        doc.nodes[node as int].parent is None,
    ensures
        insert_shape(doc, node, parent, child),
{
    theorem_insert_any_wf(doc, node, parent, child);
    let d2 = insert_any(doc, node, parent, child);
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    if let Some(c) = child {
        let paths = lemma_wf_witness(doc);
        lemma_wf_split(doc, paths);
        assert(kids.contains(c));
        lemma_index_of(kids, c);
    }
    assert(node != parent);
    assert(adopt(doc, node) == doc);
    assert(d2 == insert(doc, node, parent, child));
    match child {
        None => {
            assert(kids.push(node) =~= kids + seq![node]);
            assert(kids.subrange(0, k) =~= kids);
            assert(kids.subrange(k, kids.len() as int) =~= Seq::<NodeId>::empty());
            assert(kids + seq![node] + Seq::<NodeId>::empty() =~= kids + seq![node]);
        },
        Some(c) => {
            assert(kids.insert(k, node) =~= kids.subrange(0, k) + seq![node] + kids.subrange(k, kids.len() as int));
        },
    }
    assert forall|x: int| 0 <= x < doc.nodes.len() && x != parent implies (#[trigger] d2.nodes[x]).children == doc.nodes[x].children
        || d2.nodes[x].children.len() == 0 by {
        assert(d2.nodes[x].children == doc.nodes[x].children);
    }
}

/// Inserting a node that has no parent (or a fragment) changes only
/// `parent`'s children, to `p + nodes + s`, and, for a fragment, empties
/// the fragment.
pub proof fn lemma_insert_any_shape(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        doc.nodes[node as int].parent is None,
    ensures
        insert_shape(doc, node, parent, child),
{
    if doc.nodes[node as int].kind is DocumentFragment {
        lemma_insert_any_shape_frag(doc, node, parent, child);
    } else {
        lemma_insert_any_shape_node(doc, node, parent, child);
    }
}

// ---------------------------------------------------------------------
// Pre-insert

/// A call that passes steps 1 to 4 of "ensure pre-insertion validity":
/// `parent` may have children, `node` is not a host-including inclusive
/// ancestor of it, `child` (if any) is one of its children, and `node` is
/// not a document. (And, a restriction of this theorem and not a step,
/// `child` is not `node`.)
pub open spec fn pre_insert_steps_1_to_4(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& insert_any_requires(doc, node, parent, child)
    &&& !is_host_including_inclusive_ancestor(doc, node, parent)
}

/// A fragment's children are not doctypes, where the rules hold.
proof fn lemma_fragment_children_not_doctype(doc: Document, node: NodeId)
    requires
        children_rules_hold(doc),
        valid(doc, node),
        doc.nodes[node as int].kind is DocumentFragment,
    ensures
        forall|j: int| 0 <= j < doc.nodes[node as int].children.len() ==> !(doc.nodes[#[trigger] doc.nodes[node as int].children[j] as int].kind is DocumentType),
{
}

/// What inserting `node` between `p` and `s` needs, for the rules to stay
/// true: a document takes no `Text` node and no [`rules_violation`]; any
/// other parent takes no doctype.
pub open spec fn insert_rules_condition(doc: Document, node: NodeId, parent: NodeId, p: Seq<NodeId>, s: Seq<NodeId>) -> bool {
    if doc.nodes[parent as int].kind is Document {
        !(doc.nodes[node as int].kind is Text) && !rules_violation(doc, node, p, s)
    } else {
        !(doc.nodes[node as int].kind is DocumentType)
    }
}

/// [`insert_rules_condition`] for an insertion of `node` into `parent`
/// before `child`.
pub open spec fn pre_insert_condition(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    insert_rules_condition(doc, node, parent, kids.subrange(0, k), kids.subrange(k, kids.len() as int))
}

/// Inserting a node that has no parent (or a fragment), in an arena where
/// the rules hold, leaves the rules true exactly when
/// [`pre_insert_condition`] holds. (This says nothing of the checks of
/// "ensure pre-insertion validity".)
#[verifier::rlimit(100)]
pub proof fn lemma_insert_rules_iff(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
    ensures
        children_rules_hold(insert_any(doc, node, parent, child)) <==> pre_insert_condition(doc, node, parent, child),
{
    lemma_insert_any_shape(doc, node, parent, child);
    let d2 = insert_any(doc, node, parent, child);
    let kids = children(doc, parent);
    let k = split_index(kids, child);
    let p = kids.subrange(0, k);
    let s = kids.subrange(k, kids.len() as int);
    let ins = inserted_nodes(doc, node);
    let q = p + ins + s;
    lemma_rules_shape(doc, d2, parent, q);
    assert(p + s =~= kids);
    if doc.nodes[node as int].kind is DocumentFragment {
        lemma_fragment_children_not_doctype(doc, node);
    }
    if doc.nodes[parent as int].kind is Document {
        let paths = lemma_wf_witness(doc);
        lemma_wf_split(doc, paths);
        assert(parent == 0);
        assert(document_children_ok(doc, p + s));
        lemma_ok_insert_node(doc, node, p, s);
    } else {
        assert(forall|j: int| 0 <= j < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is DocumentType));
        if doc.nodes[node as int].kind is DocumentType {
            assert(ins == seq![node]);
            assert(q[p.len() as int] == node);
        } else {
            assert forall|j: int| 0 <= j < q.len() implies !(doc.nodes[#[trigger] q[j] as int].kind is DocumentType) by {
                if j < p.len() {
                    assert(q[j] == p[j]);
                    assert(p[j] == kids[j]);
                } else if j < p.len() + ins.len() {
                    assert(q[j] == ins[j - p.len()]);
                } else {
                    assert(q[j] == s[j - p.len() - ins.len()]);
                    assert(s[j - p.len() - ins.len()] == kids[k + j - p.len() - ins.len()]);
                }
            }
        }
    }
}

/// For a call that passes steps 1 to 4, with a node that has no parent,
/// in an arena where the rules hold: it passes steps 5 and 6 exactly when
/// inserting leaves the rules true.
pub proof fn lemma_pre_insert_exact(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        pre_insert_steps_1_to_4(doc, node, parent, child),
    ensures
        pre_insert_error(doc, node, parent, child) is None <==> children_rules_hold(insert_any(doc, node, parent, child)),
{
    lemma_insert_rules_iff(doc, node, parent, child);
    lemma_pre_insert_violation(doc, node, parent, child);
    assert(pre_insert_error(doc, node, parent, child) is None <==> pre_insert_condition(doc, node, parent, child));
}

/// DOM §4.2.3† "ensure pre-insertion validity", steps 5 and 6: "pre-insert"
/// a node that has no parent (a fragment never has one), in an arena where
/// [`children_rules_hold`], leaves the rules true. And the checks are
/// exact: for a call that passes steps 1 to 4, the call passes them (no
/// error) exactly when inserting without them would leave the rules true.
/// So a `Text` node is refused as a document's child, a doctype as any
/// other node's child, and the document keeps at most one element and one
/// doctype, the doctype first.
pub proof fn theorem_pre_insert_children_rules(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
    ensures
        children_rules_hold(pre_insert(doc, node, parent, child)),
        pre_insert_steps_1_to_4(doc, node, parent, child) ==> (pre_insert_error(doc, node, parent, child) is None <==> children_rules_hold(
            insert_any(doc, node, parent, child),
        )),
{
    if pre_insert_steps_1_to_4(doc, node, parent, child) {
        lemma_pre_insert_exact(doc, node, parent, child);
    }
    if pre_insert_error(doc, node, parent, child) is None {
        lemma_pre_insert_valid(doc, node, parent, child);
        // `child` is not `node`: step 3 passed, and `node` has no parent.
        if child == Some(node) {
            assert(doc.nodes[node as int].parent == Some(parent));
        }
        assert(pre_insert_reference(doc, node, child) == child);
        lemma_not_host_not_incl(doc, node, parent);
        assert(pre_insert_steps_1_to_4(doc, node, parent, child));
        lemma_pre_insert_exact(doc, node, parent, child);
    }
}

// ---------------------------------------------------------------------
// Replace

/// A call that passes steps 1 to 4 of "replace": `parent` may have
/// children, `node` is not a host-including inclusive ancestor of it,
/// `child`'s parent is `parent`, and `node` is not a document.
pub open spec fn replace_steps_1_to_4(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> bool {
    &&& may_have_children(doc.nodes[parent as int].kind)
    &&& !is_host_including_inclusive_ancestor(doc, node, parent)
    &&& doc.nodes[child as int].parent == Some(parent)
    &&& !(doc.nodes[node as int].kind is Document)
}

/// "Replace" without its checks: steps 7 to 13, as [`replace`] runs them
/// on a call without an error.
pub open spec fn replace_unchecked(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> Document {
    insert_any(remove(doc, child), node, parent, replace_reference(doc, child, node))
}

/// A call that passes steps 1 to 4 of "replace" meets what [`insert_any`]
/// asks, after `child` is removed, with the reference child of steps 7 and
/// 8 ([`lemma_replace_valid`], which assumes steps 5 and 6 pass too).
pub proof fn lemma_replace_valid_steps_1_to_4(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        replace_steps_1_to_4(doc, child, node, parent),
    ensures
        remove_requires(doc, child),
        insert_any_requires(remove(doc, child), node, parent, replace_reference(doc, child, node)),
{
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

/// What [`lemma_replace_shape`] says.
pub open spec fn replace_shape(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> bool {
    let d2 = replace_unchecked(doc, child, node, parent);
    let kids = children(doc, parent);
    let i = index_of(kids, child);
    &&& wf(d2)
    &&& d2.nodes.len() == doc.nodes.len()
    &&& forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind
    &&& 0 <= i < kids.len()
    &&& kids.subrange(0, i) + seq![child] + kids.subrange(i + 1, kids.len() as int) == kids
    &&& d2.nodes[parent as int].children == kids.subrange(0, i) + inserted_nodes(doc, node) + kids.subrange(i + 1, kids.len() as int)
    &&& forall|x: int|
        0 <= x < doc.nodes.len() && x != parent ==> (#[trigger] d2.nodes[x]).children == doc.nodes[x].children || d2.nodes[x].children.len() == 0
}

/// "Replace" of `child` by a node that has no parent changes only
/// `parent`'s children, to `child`'s place taken by the node's, and, for a
/// fragment, empties the fragment.
#[verifier::rlimit(100)]
pub proof fn lemma_replace_shape(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        replace_steps_1_to_4(doc, child, node, parent),
        doc.nodes[node as int].parent is None,
    ensures
        replace_shape(doc, child, node, parent),
{
    lemma_replace_valid_steps_1_to_4(doc, child, node, parent);
    let d1 = remove(doc, child);
    theorem_remove_wf(doc, child);
    theorem_remove_keeps_record(doc, child);
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
    let r = replace_reference(doc, child, node);
    let kids = children(doc, parent);
    assert(kids.contains(child));
    lemma_index_of(kids, child);
    let i = index_of(kids, child);
    let pre = kids.subrange(0, i);
    let suf = kids.subrange(i + 1, kids.len() as int);
    assert(pre + seq![child] + suf =~= kids);
    assert(node != child);
    assert(d1.nodes[node as int].parent is None);
    // The children of `parent` after the removal.
    let kids1 = children(d1, parent);
    assert(d1.nodes == doc.nodes.update(parent as int, Node { children: kids.remove(i), ..doc.nodes[parent as int] }).update(
        child as int,
        Node { parent: None, ..doc.nodes[child as int] },
    ));
    assert(child != parent);
    assert(kids1 == kids.remove(i));
    assert(kids.remove(i) =~= pre + suf);
    lemma_insert_any_shape(d1, node, parent, r);
    let d2 = replace_unchecked(doc, child, node, parent);
    assert(d2 == insert_any(d1, node, parent, r));
    assert(node != parent);
    assert(inserted_nodes(d1, node) == inserted_nodes(doc, node));
    lemma_next_sibling(doc, child);
    // `node` is not `child`'s next sibling (that has a parent, `node` has none).
    assert(r == next_sibling(doc, child));
    let paths1 = lemma_wf_witness(d1);
    lemma_wf_split(d1, paths1);
    assert(kids1.no_duplicates());
    match r {
        None => {
            assert(i + 1 == kids.len());
            assert(suf =~= Seq::<NodeId>::empty());
            assert(kids1.subrange(0, kids1.len() as int) =~= kids1);
            assert(kids1.subrange(kids1.len() as int, kids1.len() as int) =~= Seq::<NodeId>::empty());
            assert(pre =~= kids1);
        },
        Some(x) => {
            assert(i + 1 < kids.len());
            assert(x == kids[i + 1]);
            assert(kids1[i] == x);
            lemma_index_of_unique(kids1, i);
            assert(kids1.subrange(0, i) =~= pre);
            assert(kids1.subrange(i, kids1.len() as int) =~= suf);
        },
    }
    assert forall|x: int| 0 <= x < doc.nodes.len() && x != parent implies (#[trigger] d2.nodes[x]).children == doc.nodes[x].children
        || d2.nodes[x].children.len() == 0 by {
        assert(d1.nodes[x].children == doc.nodes[x].children);
    }
}

/// [`insert_rules_condition`] for the replacement of `child` by `node`.
pub open spec fn replace_condition(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> bool {
    let kids = children(doc, parent);
    let i = index_of(kids, child);
    insert_rules_condition(doc, node, parent, kids.subrange(0, i), kids.subrange(i + 1, kids.len() as int))
}

/// Replacing `child` by a node that has no parent (or a fragment), in an
/// arena where the rules hold, leaves the rules true exactly when
/// [`replace_condition`] holds. (This says nothing of the checks of
/// "replace".)
#[verifier::rlimit(100)]
pub proof fn lemma_replace_rules_iff(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        replace_steps_1_to_4(doc, child, node, parent),
    ensures
        children_rules_hold(replace_unchecked(doc, child, node, parent)) <==> replace_condition(doc, child, node, parent),
{
    lemma_replace_shape(doc, child, node, parent);
    let d2 = replace_unchecked(doc, child, node, parent);
    let kids = children(doc, parent);
    let i = index_of(kids, child);
    let p = kids.subrange(0, i);
    let s = kids.subrange(i + 1, kids.len() as int);
    let ins = inserted_nodes(doc, node);
    let q = p + ins + s;
    lemma_rules_shape(doc, d2, parent, q);
    if doc.nodes[node as int].kind is DocumentFragment {
        lemma_fragment_children_not_doctype(doc, node);
    }
    if doc.nodes[parent as int].kind is Document {
        let paths = lemma_wf_witness(doc);
        lemma_wf_split(doc, paths);
        assert(parent == 0);
        assert(document_children_ok(doc, p + seq![child] + s));
        lemma_ok_drop_mid(doc, p, seq![child], s);
        lemma_ok_insert_node(doc, node, p, s);
    } else {
        assert(forall|j: int| 0 <= j < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is DocumentType));
        if doc.nodes[node as int].kind is DocumentType {
            assert(ins == seq![node]);
            assert(q[p.len() as int] == node);
        } else {
            assert forall|j: int| 0 <= j < q.len() implies !(doc.nodes[#[trigger] q[j] as int].kind is DocumentType) by {
                if j < p.len() {
                    assert(q[j] == p[j]);
                    assert(p[j] == kids[j]);
                } else if j < p.len() + ins.len() {
                    assert(q[j] == ins[j - p.len()]);
                } else {
                    assert(q[j] == s[j - p.len() - ins.len()]);
                    assert(s[j - p.len() - ins.len()] == kids[i + 1 + j - p.len() - ins.len()]);
                }
            }
        }
    }
}

/// For a call that passes steps 1 to 4, with a node that has no parent,
/// in an arena where the rules hold: it passes steps 5 and 6 of "replace"
/// exactly when replacing leaves the rules true.
pub proof fn lemma_replace_exact(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        replace_steps_1_to_4(doc, child, node, parent),
    ensures
        replace_error(doc, child, node, parent) is None <==> children_rules_hold(replace_unchecked(doc, child, node, parent)),
{
    lemma_replace_rules_iff(doc, child, node, parent);
    lemma_replace_violation(doc, child, node, parent);
    assert(replace_error(doc, child, node, parent) is None <==> replace_condition(doc, child, node, parent));
}

/// DOM §4.2.3† "replace", steps 5 and 6: replacing a child with a node
/// that has no parent (a fragment never has one), in an arena where
/// [`children_rules_hold`], leaves the rules true. And the checks are
/// exact: for a call that passes steps 1 to 4, the call passes them
/// exactly when replacing without them would leave the rules true. The
/// replaced child itself does not count against the new node, so a
/// document's element may be replaced by another element, and its doctype
/// by another doctype.
pub proof fn theorem_replace_children_rules(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
    ensures
        children_rules_hold(replace(doc, child, node, parent)),
        replace_steps_1_to_4(doc, child, node, parent) ==> (replace_error(doc, child, node, parent) is None <==> children_rules_hold(
            replace_unchecked(doc, child, node, parent),
        )),
{
    if replace_steps_1_to_4(doc, child, node, parent) {
        lemma_replace_exact(doc, child, node, parent);
    }
    if replace_error(doc, child, node, parent) is None {
        lemma_not_host_not_incl(doc, node, parent);
        assert(replace_steps_1_to_4(doc, child, node, parent));
        lemma_replace_exact(doc, child, node, parent);
        assert(replace(doc, child, node, parent) == replace_unchecked(doc, child, node, parent));
    }
}

// ---------------------------------------------------------------------
// For the kill certificates of `mutations.json`: building arenas where the
// rules hold, and what the theorems say of a call, in terms of the
// condition that does not read the checks.

/// A new document obeys the rules.
pub proof fn lemma_new_document_rules(url: Seq<u32>)
    ensures
        children_rules_hold(new_document(url)),
{
    let d = new_document(url);
    assert(d.nodes.len() == 1);
    assert(d.nodes[0].kind is Document);
    assert(d.nodes[0].children =~= Seq::<NodeId>::empty());
    assert(document_children_ok(d, d.nodes[0].children));
}

/// In a well-formed arena every child is a node of it.
pub proof fn lemma_children_valid(doc: Document)
    requires
        wf(doc),
    ensures
        forall|i: int, j: int| 0 <= i < doc.nodes.len() && 0 <= j < doc.nodes[i].children.len() ==> (#[trigger] doc.nodes[i].children[j]) < doc.nodes.len(),
{
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
}

/// Creating a node keeps the rules true: it has no children and no
/// existing node changes.
#[verifier::rlimit(100)]
pub proof fn lemma_create_keeps_rules(doc: Document, k: NodeKind)
    requires
        wf(doc),
        children_rules_hold(doc),
    ensures
        children_rules_hold(create_node(doc, k).0),
{
    let d2 = create_node(doc, k).0;
    let n = doc.nodes.len();
    lemma_children_valid(doc);
    assert(d2.nodes.len() == n + 1);
    assert(1 <= n);
    assert forall|p: int, j: int|
        0 <= p < d2.nodes.len() && !(d2.nodes[p].kind is Document) && 0 <= j < d2.nodes[p].children.len() implies !(d2.nodes[#[trigger] d2.nodes[p].children[j] as int].kind is DocumentType) by {
        assert(p < n);
        assert(d2.nodes[p] == doc.nodes[p]);
        let c = doc.nodes[p].children[j];
        assert(c < n);
        assert(d2.nodes[c as int] == doc.nodes[c as int]);
    }
    assert(d2.nodes[0] == doc.nodes[0]);
    assert forall|x: int| 0 <= x < n implies (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind by {}
    lemma_ok_kinds(doc, d2, doc.nodes[0].children);
}

/// Appending to a parent a node that has no parent keeps the rules true
/// when [`pre_insert_condition`] holds.
pub proof fn lemma_append_keeps_rules(doc: Document, parent: NodeId, node: NodeId)
    requires
        insert_requires(doc, node, parent, None),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        pre_insert_condition(doc, node, parent, None),
    ensures
        children_rules_hold(append(doc, parent, node)),
{
    assert(insert_any_requires(doc, node, parent, None));
    assert(append(doc, parent, node) == insert_any(doc, node, parent, None));
    lemma_insert_rules_iff(doc, node, parent, None);
}

/// A call that [`pre_insert_condition`] rejects gets an error from "ensure
/// pre-insertion validity" (`theorem_pre_insert_children_rules`).
pub proof fn lemma_pre_insert_refused(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        !pre_insert_condition(doc, node, parent, child),
    ensures
        pre_insert_error(doc, node, parent, child) is Some,
{
    theorem_pre_insert_children_rules(doc, node, parent, child);
    if pre_insert_error(doc, node, parent, child) is None {
        lemma_pre_insert_valid(doc, node, parent, child);
        if child == Some(node) {
            assert(doc.nodes[node as int].parent == Some(parent));
        }
        assert(pre_insert_reference(doc, node, child) == child);
        lemma_not_host_not_incl(doc, node, parent);
        assert(pre_insert_steps_1_to_4(doc, node, parent, child));
        lemma_insert_rules_iff(doc, node, parent, child);
    }
}

/// A call that passes steps 1 to 4 and that [`pre_insert_condition`]
/// accepts gets no error from "ensure pre-insertion validity"
/// (`theorem_pre_insert_children_rules`).
pub proof fn lemma_pre_insert_accepted(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        pre_insert_steps_1_to_4(doc, node, parent, child),
        pre_insert_condition(doc, node, parent, child),
    ensures
        pre_insert_error(doc, node, parent, child) is None,
{
    theorem_pre_insert_children_rules(doc, node, parent, child);
    lemma_insert_rules_iff(doc, node, parent, child);
}

/// A call that [`replace_condition`] rejects gets an error from "replace"
/// (`theorem_replace_children_rules`).
pub proof fn lemma_replace_refused(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        !replace_condition(doc, child, node, parent),
    ensures
        replace_error(doc, child, node, parent) is Some,
{
    theorem_replace_children_rules(doc, child, node, parent);
    if replace_error(doc, child, node, parent) is None {
        lemma_not_host_not_incl(doc, node, parent);
        assert(replace_steps_1_to_4(doc, child, node, parent));
        lemma_replace_rules_iff(doc, child, node, parent);
    }
}

/// A call that passes steps 1 to 4 and that [`replace_condition`] accepts
/// gets no error from "replace" (`theorem_replace_children_rules`).
pub proof fn lemma_replace_accepted(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        children_rules_hold(doc),
        doc.nodes[node as int].parent is None,
        replace_steps_1_to_4(doc, child, node, parent),
        replace_condition(doc, child, node, parent),
    ensures
        replace_error(doc, child, node, parent) is None,
{
    theorem_replace_children_rules(doc, child, node, parent);
    lemma_replace_rules_iff(doc, child, node, parent);
}

} // verus!
