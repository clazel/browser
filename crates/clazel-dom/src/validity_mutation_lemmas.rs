//! Concrete instances of the theorems of [`super::validity_lemmas`], the
//! kill certificates of the mutations of "ensure pre-insertion validity" and
//! "replace" (steps 5 and 6) in `mutations.json` (`xtask/src/mutate.rs`).
//! Each lemma says what a theorem implies about a call on a small concrete
//! arena; a certificate evaluates the mutated check on that call
//! (`compute_only`) and shows it contradicts the lemma.
//!
//! The arena [`vm_pre`]: a document (0) with nothing in it, and loose nodes:
//! a text (1), elements (2, 3), doctypes (4, 5), comments (6, 7), a fragment
//! (8) of two elements (9, 10), a fragment (11) of a text (12), a fragment
//! (13) of an element (14) and an element (15). The scenarios `vm_s*` put
//! some of them in the document, or comment 7 in element 15.
//!
//! The lemmas prove each call's outcome from the theorems and from
//! [`pre_insert_condition`] and [`replace_condition`], which do not read the
//! checks. The `compute_only` assertions evaluate only what no mutation
//! changes: the arenas, and those conditions.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[cfg(verus_only)]
use super::mutation_lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::validity_lemmas::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A doctype with empty strings.
pub open spec fn vm_doctype() -> NodeKind {
    NodeKind::DocumentType { name: seq![], public_id: seq![], system_id: seq![] }
}

/// A comment with no data.
pub open spec fn vm_comment() -> NodeKind {
    NodeKind::Comment { data: seq![] }
}

/// What a call of "append" needs, apart from the arena being well formed:
/// [`insert_requires`], the node has no parent, and the rules stay true.
pub open spec fn vm_append_ok(d: Document, parent: NodeId, node: NodeId) -> bool {
    &&& valid(d, node)
    &&& valid(d, parent)
    &&& !(d.nodes[node as int].kind is Document)
    &&& !(d.nodes[node as int].kind is DocumentFragment)
    &&& may_have_children(d.nodes[parent as int].kind)
    &&& !is_inclusive_ancestor(d, node, parent)
    &&& d.nodes[node as int].parent is None
    &&& pre_insert_condition(d, node, parent, None)
}

/// What a call of "ensure pre-insertion validity" needs to pass steps 1 to
/// 4, apart from the arena being well formed.
pub open spec fn vm_steps(d: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& valid(d, node)
    &&& valid(d, parent)
    &&& !(d.nodes[node as int].kind is Document)
    &&& may_have_children(d.nodes[parent as int].kind)
    &&& !is_inclusive_ancestor(d, node, parent)
    &&& match child {
        None => true,
        Some(c) => valid(d, c) && c != node && d.nodes[c as int].parent == Some(parent),
    }
    &&& !is_host_including_inclusive_ancestor(d, node, parent)
}

/// Creating a node in an arena where the rules hold keeps both.
proof fn vm_create(d: Document, k: NodeKind)
    requires
        wf(d),
        children_rules_hold(d),
        creatable(d, k),
        d.nodes.len() + 1 <= max_nodes(),
    ensures
        wf(create_node(d, k).0),
        children_rules_hold(create_node(d, k).0),
        create_node(d, k).0.nodes.len() == d.nodes.len() + 1,
{
    theorem_create_node_wf(d, k);
    lemma_create_keeps_rules(d, k);
}

/// Appending in an arena where the rules hold keeps both.
proof fn vm_append(d: Document, parent: NodeId, node: NodeId)
    requires
        wf(d),
        children_rules_hold(d),
        vm_append_ok(d, parent, node),
    ensures
        wf(append(d, parent, node)),
        children_rules_hold(append(d, parent, node)),
        append(d, parent, node).nodes.len() == d.nodes.len(),
{
    assert(insert_requires(d, node, parent, None));
    theorem_append_wf(d, parent, node);
    lemma_append_keeps_rules(d, parent, node);
}

/// The document, then each loose node created in turn.
pub open spec fn vm_d0() -> Document {
    new_document(seq![])
}

/// Node 1 created.
pub open spec fn vm_d1() -> Document {
    create_node(vm_d0(), ml_text()).0
}

/// Node 2 created.
pub open spec fn vm_d2() -> Document {
    create_node(vm_d1(), ml_element()).0
}

/// Node 3 created.
pub open spec fn vm_d3() -> Document {
    create_node(vm_d2(), ml_element()).0
}

/// Node 4 created.
pub open spec fn vm_d4() -> Document {
    create_node(vm_d3(), vm_doctype()).0
}

/// Node 5 created.
pub open spec fn vm_d5() -> Document {
    create_node(vm_d4(), vm_doctype()).0
}

/// Node 6 created.
pub open spec fn vm_d6() -> Document {
    create_node(vm_d5(), vm_comment()).0
}

/// Node 7 created.
pub open spec fn vm_d7() -> Document {
    create_node(vm_d6(), vm_comment()).0
}

/// Node 8 created.
pub open spec fn vm_d8() -> Document {
    create_node(vm_d7(), NodeKind::DocumentFragment { host: None }).0
}

/// Node 9 created.
pub open spec fn vm_d9() -> Document {
    create_node(vm_d8(), ml_element()).0
}

/// Node 10 created.
pub open spec fn vm_d10() -> Document {
    create_node(vm_d9(), ml_element()).0
}

/// Node 11 created.
pub open spec fn vm_d11() -> Document {
    create_node(vm_d10(), NodeKind::DocumentFragment { host: None }).0
}

/// Node 12 created.
pub open spec fn vm_d12() -> Document {
    create_node(vm_d11(), ml_text()).0
}

/// Node 13 created.
pub open spec fn vm_d13() -> Document {
    create_node(vm_d12(), NodeKind::DocumentFragment { host: None }).0
}

/// Node 14 created.
pub open spec fn vm_d14() -> Document {
    create_node(vm_d13(), ml_element()).0
}

/// Node 15 created.
pub open spec fn vm_d15() -> Document {
    create_node(vm_d14(), ml_element()).0
}

/// Node 9 appended to the fragment or element 8.
pub open spec fn vm_a1() -> Document {
    append(vm_d15(), 8, 9)
}

/// Node 10 appended to the fragment or element 8.
pub open spec fn vm_a2() -> Document {
    append(vm_a1(), 8, 10)
}

/// Node 12 appended to the fragment or element 11.
pub open spec fn vm_a3() -> Document {
    append(vm_a2(), 11, 12)
}

/// Node 14 appended to the fragment or element 13.
pub open spec fn vm_a4() -> Document {
    append(vm_a3(), 13, 14)
}

/// The base arena, [`vm_pre`]: the loose nodes, the fragments filled.
pub open spec fn vm_pre() -> Document {
    vm_a4()
}

/// The base arena is well formed, obeys the rules, and has 16 nodes.
#[verifier::rlimit(400)]
pub proof fn vm_pre_ok()
    ensures
        wf(vm_pre()),
        children_rules_hold(vm_pre()),
        vm_pre().nodes.len() == 16,
{
    theorem_new_document_wf(seq![]);
    lemma_new_document_rules(seq![]);
    assert(creatable(vm_d0(), ml_text())) by (compute_only);
    vm_create(vm_d0(), ml_text());
    assert(creatable(vm_d1(), ml_element())) by (compute_only);
    vm_create(vm_d1(), ml_element());
    assert(creatable(vm_d2(), ml_element())) by (compute_only);
    vm_create(vm_d2(), ml_element());
    assert(creatable(vm_d3(), vm_doctype())) by (compute_only);
    vm_create(vm_d3(), vm_doctype());
    assert(creatable(vm_d4(), vm_doctype())) by (compute_only);
    vm_create(vm_d4(), vm_doctype());
    assert(creatable(vm_d5(), vm_comment())) by (compute_only);
    vm_create(vm_d5(), vm_comment());
    assert(creatable(vm_d6(), vm_comment())) by (compute_only);
    vm_create(vm_d6(), vm_comment());
    assert(creatable(vm_d7(), NodeKind::DocumentFragment { host: None })) by (compute_only);
    vm_create(vm_d7(), NodeKind::DocumentFragment { host: None });
    assert(creatable(vm_d8(), ml_element())) by (compute_only);
    vm_create(vm_d8(), ml_element());
    assert(creatable(vm_d9(), ml_element())) by (compute_only);
    vm_create(vm_d9(), ml_element());
    assert(creatable(vm_d10(), NodeKind::DocumentFragment { host: None })) by (compute_only);
    vm_create(vm_d10(), NodeKind::DocumentFragment { host: None });
    assert(creatable(vm_d11(), ml_text())) by (compute_only);
    vm_create(vm_d11(), ml_text());
    assert(creatable(vm_d12(), NodeKind::DocumentFragment { host: None })) by (compute_only);
    vm_create(vm_d12(), NodeKind::DocumentFragment { host: None });
    assert(creatable(vm_d13(), ml_element())) by (compute_only);
    vm_create(vm_d13(), ml_element());
    assert(creatable(vm_d14(), ml_element())) by (compute_only);
    vm_create(vm_d14(), ml_element());
    assert(vm_append_ok(vm_d15(), 8, 9)) by (compute_only);
    vm_append(vm_d15(), 8, 9);
    assert(vm_append_ok(vm_a1(), 8, 10)) by (compute_only);
    vm_append(vm_a1(), 8, 10);
    assert(vm_append_ok(vm_a2(), 11, 12)) by (compute_only);
    vm_append(vm_a2(), 11, 12);
    assert(vm_append_ok(vm_a3(), 13, 14)) by (compute_only);
    vm_append(vm_a3(), 13, 14);
}

/// The scenario `s1`: node 2 appended to node 0 of [`vm_pre`].
pub open spec fn vm_s1() -> Document {
    append(vm_pre(), 0, 2)
}

/// The scenario `s1` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s1_ok()
    ensures
        wf(vm_s1()),
        children_rules_hold(vm_s1()),
        vm_s1().nodes.len() == 16,
{
    vm_pre_ok();
    assert(vm_append_ok(vm_pre(), 0, 2)) by (compute_only);
    vm_append(vm_pre(), 0, 2);
}

/// The scenario `s2`: node 4 appended to node 0 of [`vm_pre`].
pub open spec fn vm_s2() -> Document {
    append(vm_pre(), 0, 4)
}

/// The scenario `s2` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s2_ok()
    ensures
        wf(vm_s2()),
        children_rules_hold(vm_s2()),
        vm_s2().nodes.len() == 16,
{
    vm_pre_ok();
    assert(vm_append_ok(vm_pre(), 0, 4)) by (compute_only);
    vm_append(vm_pre(), 0, 4);
}

/// The scenario `s6`: node 6 appended to node 0 of [`vm_pre`].
pub open spec fn vm_s6() -> Document {
    append(vm_pre(), 0, 6)
}

/// The scenario `s6` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s6_ok()
    ensures
        wf(vm_s6()),
        children_rules_hold(vm_s6()),
        vm_s6().nodes.len() == 16,
{
    vm_pre_ok();
    assert(vm_append_ok(vm_pre(), 0, 6)) by (compute_only);
    vm_append(vm_pre(), 0, 6);
}

/// The scenario `s9`: node 7 appended to node 15 of [`vm_pre`].
pub open spec fn vm_s9() -> Document {
    append(vm_pre(), 15, 7)
}

/// The scenario `s9` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s9_ok()
    ensures
        wf(vm_s9()),
        children_rules_hold(vm_s9()),
        vm_s9().nodes.len() == 16,
{
    vm_pre_ok();
    assert(vm_append_ok(vm_pre(), 15, 7)) by (compute_only);
    vm_append(vm_pre(), 15, 7);
}

/// The scenario `s3`: node 4 appended to node 0 of [`vm_s6`].
pub open spec fn vm_s3() -> Document {
    append(vm_s6(), 0, 4)
}

/// The scenario `s3` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s3_ok()
    ensures
        wf(vm_s3()),
        children_rules_hold(vm_s3()),
        vm_s3().nodes.len() == 16,
{
    vm_s6_ok();
    assert(vm_append_ok(vm_s6(), 0, 4)) by (compute_only);
    vm_append(vm_s6(), 0, 4);
}

/// The scenario `s4`: node 6 appended to node 0 of [`vm_s1`].
pub open spec fn vm_s4() -> Document {
    append(vm_s1(), 0, 6)
}

/// The scenario `s4` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s4_ok()
    ensures
        wf(vm_s4()),
        children_rules_hold(vm_s4()),
        vm_s4().nodes.len() == 16,
{
    vm_s1_ok();
    assert(vm_append_ok(vm_s1(), 0, 6)) by (compute_only);
    vm_append(vm_s1(), 0, 6);
}

/// The scenario `s8`: node 6 appended to node 0 of [`vm_s2`].
pub open spec fn vm_s8() -> Document {
    append(vm_s2(), 0, 6)
}

/// The scenario `s8` is well formed, obeys the rules, and has 16 nodes.
pub proof fn vm_s8_ok()
    ensures
        wf(vm_s8()),
        children_rules_hold(vm_s8()),
        vm_s8().nodes.len() == 16,
{
    vm_s2_ok();
    assert(vm_append_ok(vm_s2(), 0, 6)) by (compute_only);
    vm_append(vm_s2(), 0, 6);
}

/// Step 5: a `Text` node is refused as a document's child.
pub proof fn vm_pi_text_in_document()
    ensures
        pre_insert_error(vm_pre(), 1, 0, None) is Some,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[1].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_pre(), 1, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 1, 0, None);
}

/// Step 5: a doctype is refused as a non-document's child.
pub proof fn vm_pi_doctype_in_element()
    ensures
        pre_insert_error(vm_pre(), 5, 15, None) is Some,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[5].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_pre(), 5, 15, None)) by (compute_only);
    lemma_pre_insert_refused(d, 5, 15, None);
}

/// Step 6, fragment: more than one element child is refused.
pub proof fn vm_pi_fragment_two_elements()
    ensures
        pre_insert_error(vm_pre(), 8, 0, None) is Some,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[8].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_pre(), 8, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 8, 0, None);
}

/// Step 6, fragment: a `Text` child is refused.
pub proof fn vm_pi_fragment_text()
    ensures
        pre_insert_error(vm_pre(), 11, 0, None) is Some,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[11].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_pre(), 11, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 11, 0, None);
}

/// Step 6, fragment of one element: refused if the parent has an element child.
pub proof fn vm_pi_fragment_element_parent_element()
    ensures
        pre_insert_error(vm_s1(), 13, 0, None) is Some,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[13].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s1(), 13, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 13, 0, None);
}

/// Step 6, fragment of one element: refused if the child is a doctype.
pub proof fn vm_pi_fragment_element_before_doctype()
    ensures
        pre_insert_error(vm_s2(), 13, 0, Some(4usize)) is Some,
{
    vm_s2_ok();
    let d = vm_s2();
    assert(vm_s2().nodes[13].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s2(), 13, 0, Some(4usize))) by (compute_only);
    lemma_pre_insert_refused(d, 13, 0, Some(4usize));
}

/// Step 6, fragment of one element: refused if a doctype is following the child.
pub proof fn vm_pi_fragment_element_doctype_after()
    ensures
        pre_insert_error(vm_s3(), 13, 0, Some(6usize)) is Some,
{
    vm_s3_ok();
    let d = vm_s3();
    assert(vm_s3().nodes[13].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s3(), 13, 0, Some(6usize))) by (compute_only);
    lemma_pre_insert_refused(d, 13, 0, Some(6usize));
}

/// Step 6, element: refused if the parent has an element child.
pub proof fn vm_pi_element_parent_element()
    ensures
        pre_insert_error(vm_s1(), 3, 0, None) is Some,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[3].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s1(), 3, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 3, 0, None);
}

/// Step 6, element: refused if the child is a doctype.
pub proof fn vm_pi_element_before_doctype()
    ensures
        pre_insert_error(vm_s2(), 3, 0, Some(4usize)) is Some,
{
    vm_s2_ok();
    let d = vm_s2();
    assert(vm_s2().nodes[3].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s2(), 3, 0, Some(4usize))) by (compute_only);
    lemma_pre_insert_refused(d, 3, 0, Some(4usize));
}

/// Step 6, element: refused if a doctype is following the child.
pub proof fn vm_pi_element_doctype_after()
    ensures
        pre_insert_error(vm_s3(), 3, 0, Some(6usize)) is Some,
{
    vm_s3_ok();
    let d = vm_s3();
    assert(vm_s3().nodes[3].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s3(), 3, 0, Some(6usize))) by (compute_only);
    lemma_pre_insert_refused(d, 3, 0, Some(6usize));
}

/// Step 6, doctype: refused if the parent has a doctype child.
pub proof fn vm_pi_doctype_parent_doctype()
    ensures
        pre_insert_error(vm_s2(), 5, 0, None) is Some,
{
    vm_s2_ok();
    let d = vm_s2();
    assert(vm_s2().nodes[5].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s2(), 5, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 5, 0, None);
}

/// Step 6, doctype: refused if an element is preceding the child.
pub proof fn vm_pi_doctype_element_preceding()
    ensures
        pre_insert_error(vm_s4(), 5, 0, Some(6usize)) is Some,
{
    vm_s4_ok();
    let d = vm_s4();
    assert(vm_s4().nodes[5].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s4(), 5, 0, Some(6usize))) by (compute_only);
    lemma_pre_insert_refused(d, 5, 0, Some(6usize));
}

/// Step 6, doctype: appended after an element child is refused.
pub proof fn vm_pi_doctype_after_element()
    ensures
        pre_insert_error(vm_s1(), 5, 0, None) is Some,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[5].parent is None) by (compute_only);
    assert(!pre_insert_condition(vm_s1(), 5, 0, None)) by (compute_only);
    lemma_pre_insert_refused(d, 5, 0, None);
}

/// A fragment of one element is accepted into an empty document.
pub proof fn vm_pi_fragment_one_element()
    ensures
        pre_insert_error(vm_pre(), 13, 0, None) is None,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[13].parent is None) by (compute_only);
    assert(vm_steps(vm_pre(), 13, 0, None)) by (compute_only);
    assert(pre_insert_steps_1_to_4(d, 13, 0, None));
    assert(pre_insert_condition(vm_pre(), 13, 0, None)) by (compute_only);
    lemma_pre_insert_accepted(d, 13, 0, None);
}

/// A `Text` node is accepted as an element's child.
pub proof fn vm_pi_text_in_element()
    ensures
        pre_insert_error(vm_pre(), 1, 15, None) is None,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[1].parent is None) by (compute_only);
    assert(vm_steps(vm_pre(), 1, 15, None)) by (compute_only);
    assert(pre_insert_steps_1_to_4(d, 1, 15, None));
    assert(pre_insert_condition(vm_pre(), 1, 15, None)) by (compute_only);
    lemma_pre_insert_accepted(d, 1, 15, None);
}

/// A doctype is accepted as the child of an empty document.
pub proof fn vm_pi_doctype_in_document()
    ensures
        pre_insert_error(vm_pre(), 4, 0, None) is None,
{
    vm_pre_ok();
    let d = vm_pre();
    assert(vm_pre().nodes[4].parent is None) by (compute_only);
    assert(vm_steps(vm_pre(), 4, 0, None)) by (compute_only);
    assert(pre_insert_steps_1_to_4(d, 4, 0, None));
    assert(pre_insert_condition(vm_pre(), 4, 0, None)) by (compute_only);
    lemma_pre_insert_accepted(d, 4, 0, None);
}

/// Step 5 of "replace": a `Text` node is refused as a document's child.
pub proof fn vm_rp_text_in_document()
    ensures
        replace_error(vm_s1(), 2, 1, 0) is Some,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[1].parent is None) by (compute_only);
    assert(!replace_condition(vm_s1(), 2, 1, 0)) by (compute_only);
    lemma_replace_refused(d, 2, 1, 0);
}

/// Step 5 of "replace": a doctype is refused as a non-document's child.
pub proof fn vm_rp_doctype_in_element()
    ensures
        replace_error(vm_s9(), 7, 5, 15) is Some,
{
    vm_s9_ok();
    let d = vm_s9();
    assert(vm_s9().nodes[5].parent is None) by (compute_only);
    assert(!replace_condition(vm_s9(), 7, 5, 15)) by (compute_only);
    lemma_replace_refused(d, 7, 5, 15);
}

/// Step 6 of "replace", fragment: more than one element child is refused.
pub proof fn vm_rp_fragment_two_elements()
    ensures
        replace_error(vm_s6(), 6, 8, 0) is Some,
{
    vm_s6_ok();
    let d = vm_s6();
    assert(vm_s6().nodes[8].parent is None) by (compute_only);
    assert(!replace_condition(vm_s6(), 6, 8, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 8, 0);
}

/// Step 6 of "replace", fragment: a `Text` child is refused.
pub proof fn vm_rp_fragment_text()
    ensures
        replace_error(vm_s6(), 6, 11, 0) is Some,
{
    vm_s6_ok();
    let d = vm_s6();
    assert(vm_s6().nodes[11].parent is None) by (compute_only);
    assert(!replace_condition(vm_s6(), 6, 11, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 11, 0);
}

/// Step 6 of "replace", fragment of one element: refused if the parent has another element child.
pub proof fn vm_rp_fragment_element_parent_element()
    ensures
        replace_error(vm_s4(), 6, 13, 0) is Some,
{
    vm_s4_ok();
    let d = vm_s4();
    assert(vm_s4().nodes[13].parent is None) by (compute_only);
    assert(!replace_condition(vm_s4(), 6, 13, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 13, 0);
}

/// Step 6 of "replace", fragment of one element: refused if a doctype is following the child.
pub proof fn vm_rp_fragment_element_doctype_after()
    ensures
        replace_error(vm_s3(), 6, 13, 0) is Some,
{
    vm_s3_ok();
    let d = vm_s3();
    assert(vm_s3().nodes[13].parent is None) by (compute_only);
    assert(!replace_condition(vm_s3(), 6, 13, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 13, 0);
}

/// Step 6 of "replace", element: refused if the parent has another element child.
pub proof fn vm_rp_element_parent_element()
    ensures
        replace_error(vm_s4(), 6, 3, 0) is Some,
{
    vm_s4_ok();
    let d = vm_s4();
    assert(vm_s4().nodes[3].parent is None) by (compute_only);
    assert(!replace_condition(vm_s4(), 6, 3, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 3, 0);
}

/// Step 6 of "replace", element: refused if a doctype is following the child.
pub proof fn vm_rp_element_doctype_after()
    ensures
        replace_error(vm_s3(), 6, 3, 0) is Some,
{
    vm_s3_ok();
    let d = vm_s3();
    assert(vm_s3().nodes[3].parent is None) by (compute_only);
    assert(!replace_condition(vm_s3(), 6, 3, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 3, 0);
}

/// Step 6 of "replace", doctype: refused if the parent has another doctype child.
pub proof fn vm_rp_doctype_parent_doctype()
    ensures
        replace_error(vm_s8(), 6, 5, 0) is Some,
{
    vm_s8_ok();
    let d = vm_s8();
    assert(vm_s8().nodes[5].parent is None) by (compute_only);
    assert(!replace_condition(vm_s8(), 6, 5, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 5, 0);
}

/// Step 6 of "replace", doctype: refused if an element is preceding the child.
pub proof fn vm_rp_doctype_element_preceding()
    ensures
        replace_error(vm_s4(), 6, 5, 0) is Some,
{
    vm_s4_ok();
    let d = vm_s4();
    assert(vm_s4().nodes[5].parent is None) by (compute_only);
    assert(!replace_condition(vm_s4(), 6, 5, 0)) by (compute_only);
    lemma_replace_refused(d, 6, 5, 0);
}

/// An element may replace the document's element.
pub proof fn vm_rp_element_replaces_element()
    ensures
        replace_error(vm_s1(), 2, 3, 0) is None,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[3].parent is None) by (compute_only);
    assert(replace_steps_1_to_4(vm_s1(), 2, 3, 0)) by (compute_only);
    assert(replace_condition(vm_s1(), 2, 3, 0)) by (compute_only);
    lemma_replace_accepted(d, 2, 3, 0);
}

/// A doctype may replace the document's doctype.
pub proof fn vm_rp_doctype_replaces_doctype()
    ensures
        replace_error(vm_s2(), 4, 5, 0) is None,
{
    vm_s2_ok();
    let d = vm_s2();
    assert(vm_s2().nodes[5].parent is None) by (compute_only);
    assert(replace_steps_1_to_4(vm_s2(), 4, 5, 0)) by (compute_only);
    assert(replace_condition(vm_s2(), 4, 5, 0)) by (compute_only);
    lemma_replace_accepted(d, 4, 5, 0);
}

/// A fragment of one element may replace the document's element.
pub proof fn vm_rp_fragment_replaces_element()
    ensures
        replace_error(vm_s1(), 2, 13, 0) is None,
{
    vm_s1_ok();
    let d = vm_s1();
    assert(vm_s1().nodes[13].parent is None) by (compute_only);
    assert(replace_steps_1_to_4(vm_s1(), 2, 13, 0)) by (compute_only);
    assert(replace_condition(vm_s1(), 2, 13, 0)) by (compute_only);
    lemma_replace_accepted(d, 2, 13, 0);
}

/// A `Text` node may replace an element's child.
pub proof fn vm_rp_text_in_element()
    ensures
        replace_error(vm_s9(), 7, 1, 15) is None,
{
    vm_s9_ok();
    let d = vm_s9();
    assert(vm_s9().nodes[1].parent is None) by (compute_only);
    assert(replace_steps_1_to_4(vm_s9(), 7, 1, 15)) by (compute_only);
    assert(replace_condition(vm_s9(), 7, 1, 15)) by (compute_only);
    lemma_replace_accepted(d, 7, 1, 15);
}

/// A doctype may replace a comment of an empty-of-elements document.
pub proof fn vm_rp_doctype_in_document()
    ensures
        replace_error(vm_s6(), 6, 4, 0) is None,
{
    vm_s6_ok();
    let d = vm_s6();
    assert(vm_s6().nodes[4].parent is None) by (compute_only);
    assert(replace_steps_1_to_4(vm_s6(), 6, 4, 0)) by (compute_only);
    assert(replace_condition(vm_s6(), 6, 4, 0)) by (compute_only);
    lemma_replace_accepted(d, 6, 4, 0);
}

} // verus!
