//! Executable-style specification of the DOM node tree the HTML parser
//! builds, as an arena. Nothing here runs; it defines what "correct" means.
//! Every operation cites its algorithm, and each `// N.` comment is the step
//! number in it.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - DOM Standard, Living Standard, last updated 19 October 2026, commit
//!   snapshot `3c53f93a3e1fb11ef5bd38029b7a9c97baaf0177`: §4.2 "Node tree"
//!   (§4.2.3 "Mutation algorithms": insert, append, pre-insert, remove;
//!   §4.5 "adopt"), §4.4 `Node` (node document, parent, children, previous
//!   sibling, last child, inclusive ancestor), §4.5 `Document` (mode, URL),
//!   §4.6 `DocumentType`, §4.7 `DocumentFragment` (host), §4.9 `Element`
//!   (namespace, namespace prefix, local name, attribute list, "append an
//!   attribute"), §4.10 `CharacterData` ("replace data" at the end, which is
//!   appending), §4.11 `Text`, §4.14 `Comment`.
//!   <https://dom.spec.whatwg.org/>
//! - Infra Standard, last updated 19 October 2026, commit snapshot
//!   `459b7829230ad256a690dabd315db974469af8e7`, §8 "Namespaces".
//! - HTML Standard, commit `939677714df7379fee3667040113b41c91c851e7`
//!   (26 October 2026), §4.12.3 the `template` element's "template
//!   contents" (a `DocumentFragment` whose host is the template), and
//!   §4.10.17.3 "form owner" (an element's form owner, read in Phase 6).
//!
//! Modelling choices (each a deliberate difference in form, never in
//! meaning, or a stated restriction):
//! - **A document is an arena.** [`Document`] is `nodes: Seq<Node>`, and a
//!   node is named by its index, a [`NodeId`]. The document node is
//!   `nodes[0]`, and every node of the arena has it as its node document
//!   ("node document" is therefore implicit; moving a node between documents
//!   is not an operation here, Phase 7 adds it). DOM's tree is "a finite
//!   hierarchical tree structure" whose parent and children are one relation;
//!   the arena stores both directions (`parent`, `children`), and [`wf`]
//!   states that they agree.
//! - **Node ids are `usize`.** An id is our handle, not a number of any
//!   standard; ids are below [`max_nodes`], far below `usize::MAX`, so the
//!   executable arena's ids are the spec's with no conversion.
//! - **Ids are never reused, and records are never deleted.** "remove"
//!   detaches a node (its parent becomes null, it leaves its parent's
//!   children) and keeps its record, as DOM does: a removed node still
//!   exists and may be inserted again. Freeing unreachable nodes is the job
//!   of Phase 7's collector.
//! - **Each node has a wrapper slot** (`wrapper`, a Phase 7 object id,
//!   always none in Phase 4) and **each element a form owner** (`form_owner`,
//!   HTML §4.10.17.3, set by the parser when it creates the element).
//! - **Template contents are a child outside `children`.** HTML §4.12.3: a
//!   template element's template contents is a `DocumentFragment` whose
//!   host is the template; it is not one of the template's children. The
//!   element holds its id (`template_contents`) and the fragment its host's.
//! - **The operations are those the HTML parser calls, on the class of
//!   calls it makes.** DOM's "pre-insert" first "ensures pre-insert
//!   validity" and throws otherwise; the parser's calls are always valid, so
//!   the checks become preconditions ([`insert_requires`]) and the parser
//!   proves its calls meet them. Restrictions, each a precondition: the
//!   inserted node is not a `DocumentFragment` or a `Document` (insert's
//!   step 1 then gives `nodes` = « node », count 1, and step 4 does not
//!   apply), it is not an inclusive ancestor of the parent (the hierarchy
//!   check), and the reference child, if any, is a child of the parent other
//!   than the node itself (so pre-insert's "if referenceChild is node, then
//!   set referenceChild to node's next sibling" does not apply).
//! - **Out of scope, never modelled:** mutation observers and records, live
//!   ranges, `NodeIterator`s, slots, shadow trees, custom element reactions,
//!   the insertion, removing, moving, adopting and children changed steps.
//!   None of them changes the tree, and none has an effect without
//!   scripting. Steps that only touch them are listed as skipped where they
//!   would have been.
//! - **A node limit** ([`max_nodes`], 4,000,000): a node is created only
//!   while the arena holds fewer ([`can_create`]); the HTML parser treats a
//!   refusal as "stop parsing" (Phase 4 item 4.9). This is the one deliberate
//!   deviation from standards that have no limits, in the pattern of
//!   `clazel-http`'s `max_body`. The plan names `append` and `insert_before`
//!   as the operations that refuse; the arena grows only when a node is
//!   created, and every node the parser creates is created to be inserted,
//!   so the refusal is on creation, which is where the count changes.
//! - **Character data is appended, never replaced elsewhere.** HTML's
//!   "insert a character" appends to a `Text` node's data; that is "replace
//!   data" with offset = length and count 0 (§4.10), [`append_data`].
//! - **Strings are `Seq<u32>`**, code points (DOM's strings are code units;
//!   every string the parser produces is a sequence of scalar values, so the
//!   two have the same meaning here).
//! - **The document's URL and base URL** are fields the pipeline sets; the
//!   parser never reads them. HTML's "document base URL" is computed from the
//!   first `base` element by the pipeline (Phase 4 item 4.13).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A node's handle: its index in the arena.
pub type NodeId = usize;

/// The node limit (see the modelling choices).
pub open spec fn max_nodes() -> nat {
    4_000_000
}

/// Infra §8 "Namespaces": the HTML, MathML, SVG, XLink, XML and XMLNS
/// namespaces. The strings themselves ("http://www.w3.org/1999/xhtml", …) are
/// only needed to serialize, which the parser never does.
pub enum Namespace {
    /// "http://www.w3.org/1999/xhtml"
    Html,
    /// "http://www.w3.org/1998/Math/MathML"
    MathMl,
    /// "http://www.w3.org/2000/svg"
    Svg,
    /// "http://www.w3.org/1999/xlink"
    XLink,
    /// "http://www.w3.org/XML/1998/namespace"
    Xml,
    /// "http://www.w3.org/2000/xmlns/"
    Xmlns,
}

/// DOM §4.5: a document's mode, "no-quirks", "quirks" or "limited-quirks".
pub enum DocumentMode {
    /// "no-quirks", the initial value.
    NoQuirks,
    /// "quirks"
    Quirks,
    /// "limited-quirks"
    LimitedQuirks,
}

/// DOM §4.9.2 `Attr`: a namespace (null or a namespace), a namespace prefix
/// (null or a string), a local name and a value. (An attribute's element
/// and node document are implicit: it is in exactly one element's list.)
pub struct Attr {
    /// "namespace"
    pub namespace: Option<Namespace>,
    /// "namespace prefix"
    pub prefix: Option<Seq<u32>>,
    /// "local name"
    pub local_name: Seq<u32>,
    /// "value"
    pub value: Seq<u32>,
}

/// What a node is, with the fields of its interface the parser sets.
pub enum NodeKind {
    /// DOM §4.5 `Document`: its mode, URL and base URL.
    Document {
        /// "mode"
        mode: DocumentMode,
        /// "URL"
        url: Seq<u32>,
        /// HTML "document base URL", set by the pipeline.
        base_url: Seq<u32>,
    },
    /// DOM §4.6 `DocumentType`: name, public ID, system ID.
    DocumentType {
        /// "name"
        name: Seq<u32>,
        /// "public ID"
        public_id: Seq<u32>,
        /// "system ID"
        system_id: Seq<u32>,
    },
    /// DOM §4.9 `Element`.
    Element {
        /// "namespace" (null or a namespace)
        namespace: Option<Namespace>,
        /// "namespace prefix"
        prefix: Option<Seq<u32>>,
        /// "local name"
        local_name: Seq<u32>,
        /// "attribute list", in order
        attributes: Seq<Attr>,
        /// HTML §4.12.3 "template contents", for a `template` element.
        template_contents: Option<NodeId>,
        /// HTML §4.10.17.3 "form owner".
        form_owner: Option<NodeId>,
    },
    /// DOM §4.11 `Text`.
    Text {
        /// "data"
        data: Seq<u32>,
    },
    /// DOM §4.14 `Comment`.
    Comment {
        /// "data"
        data: Seq<u32>,
    },
    /// DOM §4.13 `ProcessingInstruction`: its target and (character) data.
    ProcessingInstruction {
        /// "target"
        target: Seq<u32>,
        /// "data"
        data: Seq<u32>,
    },
    /// DOM §4.7 `DocumentFragment`, with its "host".
    DocumentFragment {
        /// "host": the template whose contents this is, or null.
        host: Option<NodeId>,
    },
}

/// A node of the arena (DOM §4.4 `Node`).
pub struct Node {
    /// What the node is.
    pub kind: NodeKind,
    /// "parent": null or a node.
    pub parent: Option<NodeId>,
    /// "children": an ordered set of nodes.
    pub children: Seq<NodeId>,
    /// The wrapper slot: a Phase 7 object id, always none here.
    pub wrapper: Option<nat>,
}

/// A document: the arena. `nodes[0]` is the document node.
pub struct Document {
    /// Every node ever created in the document, by id.
    pub nodes: Seq<Node>,
}

// ---------------------------------------------------------------------
// Readers

/// `id` names a node of the arena.
pub open spec fn valid(doc: Document, id: NodeId) -> bool {
    id < doc.nodes.len()
}

/// The index of the first occurrence of `x` in `s`, or -1 if there is
/// none. (DOM §4.2 "index": "the number of its preceding siblings"; children
/// are a set, so the first occurrence is the only one.)
pub open spec fn index_of(s: Seq<NodeId>, x: NodeId) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        -1
    } else if s[0] == x {
        0
    } else {
        let r = index_of(s.drop_first(), x);
        if r < 0 {
            -1
        } else {
            r + 1
        }
    }
}

/// DOM §4.2 "parent".
pub open spec fn parent(doc: Document, n: NodeId) -> Option<NodeId> {
    doc.nodes[n as int].parent
}

/// DOM §4.2 "children".
pub open spec fn children(doc: Document, n: NodeId) -> Seq<NodeId> {
    doc.nodes[n as int].children
}

/// DOM §4.2 "previous sibling": "the first preceding sibling", null if there
/// is none (or no parent).
pub open spec fn previous_sibling(doc: Document, n: NodeId) -> Option<NodeId> {
    match parent(doc, n) {
        None => None,
        Some(p) => {
            let i = index_of(children(doc, p), n);
            if i > 0 {
                Some(children(doc, p)[i - 1])
            } else {
                None
            }
        },
    }
}

/// DOM §4.2 "last child": "its last child, if it has one, and null
/// otherwise".
pub open spec fn last_child(doc: Document, n: NodeId) -> Option<NodeId> {
    let c = children(doc, n);
    if c.len() > 0 {
        Some(c.last())
    } else {
        None
    }
}

/// HTML §13.2.6 "has a child": the node's children are not empty.
pub open spec fn has_child(doc: Document, n: NodeId) -> bool {
    children(doc, n).len() > 0
}

/// `a` is `x` or one of its first `fuel` ancestors.
pub open spec fn inclusive_ancestor_within(doc: Document, a: NodeId, x: NodeId, fuel: nat) -> bool
    decreases fuel,
{
    if x == a {
        true
    } else if fuel == 0 {
        false
    } else {
        match parent(doc, x) {
            None => false,
            Some(p) => inclusive_ancestor_within(doc, a, p, (fuel - 1) as nat),
        }
    }
}

/// DOM §4.2 "inclusive ancestor": "an object A is called an inclusive
/// ancestor of an object B if A is B or A is an ancestor of B", where an
/// ancestor is a parent or a parent's ancestor. In a well-formed arena
/// every chain of parents ends within `nodes.len()` steps
/// (`lemmas::lemma_ancestor_iff_path`), so that many steps suffice.
pub open spec fn is_inclusive_ancestor(doc: Document, a: NodeId, x: NodeId) -> bool {
    inclusive_ancestor_within(doc, a, x, doc.nodes.len())
}

/// DOM §4.2 "descendant": `x` is a descendant of `a`.
pub open spec fn is_descendant(doc: Document, x: NodeId, a: NodeId) -> bool {
    x != a && is_inclusive_ancestor(doc, a, x)
}

/// The node's kind may have children (DOM §4.2.1: a `Document`, an
/// `Element` or a `DocumentFragment`; the others are leaves).
pub open spec fn may_have_children(k: NodeKind) -> bool {
    k is Document || k is Element || k is DocumentFragment
}

// ---------------------------------------------------------------------
// Well-formedness

/// The arena's records refer only to its own nodes, and each relation is
/// stated in both directions. `paths` is a witness of acyclicity: the
/// sequence of a node's inclusive ancestors from its root down to itself.
pub open spec fn wf_with(doc: Document, paths: Seq<Seq<NodeId>>) -> bool {
    let n = doc.nodes.len();
    // The arena is not empty and within the limit; node 0 is the document
    // node, which has no parent, and no other node is a document.
    &&& 1 <= n <= max_nodes()
    &&& doc.nodes[0].kind is Document
    &&& doc.nodes[0].parent is None
    &&& forall|i: int| 0 < i < n ==> !(#[trigger] doc.nodes[i].kind is Document)
    // Parent and children agree: a node's parent lists it among its
    // children, and every child of a node has that node as its parent.
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
    // "children: an ordered set": no duplicates.
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] doc.nodes[i]).children.no_duplicates()
    // Only documents, elements and fragments have children.
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).children.len() > 0 ==> may_have_children(doc.nodes[i].kind)
    // A fragment has no parent (it is never inserted, see the restrictions).
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is DocumentFragment ==> doc.nodes[i].parent is None
    // A template's contents is a fragment whose host is that template, and
    // conversely.
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
    // A form owner is a node of the arena.
    &&& forall|i: int| 0 <= i < n && (#[trigger] doc.nodes[i]).kind is Element && doc.nodes[i].kind->Element_form_owner is Some ==>
        doc.nodes[i].kind->Element_form_owner->Some_0 < n
    // Acyclicity: each node's path is its parent's path followed by itself,
    // or itself alone if it has no parent. Paths grow by one along every
    // parent edge, so following parents always ends, at a node with no
    // parent: the document node (the root of the connected part) or a
    // detached node heading a well-formed subtree of its own.
    &&& paths.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] paths[i] == match doc.nodes[i].parent {
        None => seq![i as NodeId],
        Some(p) => paths[p as int].push(i as NodeId),
    }
}

/// A well-formed document (Phase 4 item 4.8's `wf`).
pub open spec fn wf(doc: Document) -> bool {
    exists|paths: Seq<Seq<NodeId>>| wf_with(doc, paths)
}

/// A node is connected: its root is the document node.
pub open spec fn connected(doc: Document, n: NodeId) -> bool {
    is_inclusive_ancestor(doc, 0, n)
}

// ---------------------------------------------------------------------
// Creating nodes

/// A new document (DOM §4.5 "new Document()": mode "no-quirks", the given
/// URL; its base URL is its URL until the pipeline sets it).
pub open spec fn new_document(url: Seq<u32>) -> Document {
    Document {
        nodes: seq![Node {
            kind: NodeKind::Document { mode: DocumentMode::NoQuirks, url, base_url: url },
            parent: None,
            children: seq![],
            wrapper: None,
        }],
    }
}

/// The arena may grow by `k` more nodes (see the node limit).
pub open spec fn can_create(doc: Document, k: nat) -> bool {
    doc.nodes.len() + k <= max_nodes()
}

/// What a new node may be: not a document (there is one per arena), with
/// no template contents and no host yet (those come from
/// [`create_template_contents`]), and a form owner of the arena.
pub open spec fn creatable(doc: Document, k: NodeKind) -> bool {
    match k {
        NodeKind::Document { .. } => false,
        NodeKind::Element { template_contents, form_owner, .. } => template_contents is None && match form_owner {
            None => true,
            Some(f) => valid(doc, f),
        },
        NodeKind::DocumentFragment { host } => host is None,
        _ => true,
    }
}

/// Create a node of kind `k` with no parent and no children; its id is the
/// next one. (Node creation in DOM is "create an element" §4.9, "new Text",
/// "new Comment", "new DocumentType", "new DocumentFragment": each a new
/// object whose node document is the document, with no parent.)
pub open spec fn create_node(doc: Document, k: NodeKind) -> (Document, NodeId) {
    let id = doc.nodes.len() as NodeId;
    (Document { nodes: doc.nodes.push(Node { kind: k, parent: None, children: seq![], wrapper: None }) }, id)
}

/// HTML §4.12.3: "When a template element is created, the user agent must
/// run the following steps to establish the template contents: 1. Let doc
/// be the template element's node document's appropriate template contents
/// owner document. 2. Create a DocumentFragment object whose node document
/// is doc and host is the template element. 3. Set the template element's
/// template contents to the newly created DocumentFragment object."
/// Step 1 is implicit: the arena is one document (see the modelling
/// choices; the "appropriate template contents owner document" is a second
/// document only for `importNode` and `document.implementation`, Phase 7).
pub open spec fn create_template_contents(doc: Document, t: NodeId) -> (Document, NodeId) {
    // 2.
    let (d1, f) = create_node(doc, NodeKind::DocumentFragment { host: Some(t) });
    // 3.
    let tn = d1.nodes[t as int];
    let k = match tn.kind {
        NodeKind::Element { namespace, prefix, local_name, attributes, form_owner, .. } => NodeKind::Element {
            namespace,
            prefix,
            local_name,
            attributes,
            template_contents: Some(f),
            form_owner,
        },
        other => other,
    };
    (Document { nodes: d1.nodes.update(t as int, Node { kind: k, ..tn }) }, f)
}

// ---------------------------------------------------------------------
// Mutation algorithms (DOM §4.2.3)

/// The "insertion steps" hook (DOM §4.2.3 "insert", step 7.7.1†: "Run the
/// insertion steps with inclusiveDescendant."). Other standards define
/// insertion steps for particular elements (HTML §4.12.1 `script`, §4.8.5
/// `iframe`, §4.12.3 `template`, and others). A named hook point: here the
/// hook changes nothing, and is called once, with the root of the inserted
/// subtree, from [`insert`] only. A later phase that gives a hook an effect
/// replaces this one definition, and must then re-prove the theorems of
/// `lemmas.rs` that unfold [`insert`] (each states, in its `ensures`, what
/// the hook may not change).
pub open spec fn insertion_steps(doc: Document, inserted: NodeId) -> Document {
    doc
}

/// The "removing steps" hook (DOM §4.2.3 "remove", step 12†: "Run the
/// removing steps with node and parent."). Defined by other standards for
/// particular elements, as [`insertion_steps`] is. A named hook point
/// that changes nothing here, called once from [`remove`] only, with the
/// removed node and its former parent.
pub open spec fn removing_steps(doc: Document, removed: NodeId, old_parent: NodeId) -> Document {
    doc
}

/// DOM §4.2.3 "remove" a node, the steps that change the tree: "1. Let
/// parent be node's parent. 2. Assert: parent is non-null." ... "7. Remove
/// node from its parent's children." Steps 3 to 6 and 8 onward update live
/// ranges, iterators, slots, custom elements and observers, and run the
/// removing and children changed steps, none modelled. Removing a node
/// from its parent's children makes its parent null (§4.2: a node's parent
/// is the node whose children it is in); the record stays.
pub open spec fn remove(doc: Document, node: NodeId) -> Document {
    // 1.
    let p = doc.nodes[node as int].parent->Some_0;
    let pn = doc.nodes[p as int];
    // 7.
    let i = index_of(pn.children, node);
    let removed = Document {
        nodes: doc.nodes.update(p as int, Node { children: pn.children.remove(i), ..pn }).update(
            node as int,
            Node { parent: None, ..doc.nodes[node as int] },
        ),
    };
    // 12.† "Run the removing steps with node and parent."
    removing_steps(removed, node, p)
}

/// DOM §4.5 "adopt" a node into its own node document: "1. Let oldDocument
/// be node's node document. 2. If node's parent is non-null, then remove
/// node. 3. If document is not oldDocument, …": the document is always the
/// node's own (one arena), so step 3 never applies.
pub open spec fn adopt(doc: Document, node: NodeId) -> Document {
    // 2.
    if doc.nodes[node as int].parent is Some {
        remove(doc, node)
    } else {
        doc
    }
}

/// What the parser guarantees of every call of [`insert`] (see the
/// restrictions in the modelling choices): `node` and `parent` are nodes of
/// a well-formed arena; `node` is neither a document nor a fragment, and is
/// not an inclusive ancestor of `parent` (the hierarchy check of "ensure
/// pre-insert validity", step 2); `parent` may have children (step 1); and
/// `child`, if any, is a child of `parent` (step 3) other than `node`.
pub open spec fn insert_requires(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& wf(doc)
    &&& valid(doc, node)
    &&& valid(doc, parent)
    &&& !(doc.nodes[node as int].kind is Document)
    &&& !(doc.nodes[node as int].kind is DocumentFragment)
    &&& may_have_children(doc.nodes[parent as int].kind)
    &&& !is_inclusive_ancestor(doc, node, parent)
    &&& match child {
        None => true,
        Some(c) => valid(doc, c) && c != node && doc.nodes[c as int].parent == Some(parent),
    }
}

/// DOM §4.2.3 "insert" a node `node` into `parent` before `child` (null:
/// `None`), for a `node` that is not a `DocumentFragment`:
/// "1. Let nodes be node's children, if node is a DocumentFragment node;
/// otherwise « node »." Here « node ». "2. Let count be nodes's size." 1.
/// "3. If count is 0, then return." Never. "4. If node is a DocumentFragment
/// node: …" Never. "5. If child is non-null: …" (live ranges, not
/// modelled.) "6. Let previousSibling be …" (for observers, not modelled.)
/// "7. For each node in nodes, in tree order:" (one node)
pub open spec fn insert(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Document {
    // 7.1 "Adopt node into parent's node document."
    let d1 = adopt(doc, node);
    let pn = d1.nodes[parent as int];
    let kids = match child {
        // 7.2 "If child is null, then append node to parent's children."
        None => pn.children.push(node),
        // 7.3 "Otherwise, insert node into parent's children before child's
        // index." (The index after step 7.1, which may have removed node
        // from the same parent.)
        Some(c) => pn.children.insert(index_of(pn.children, c), node),
    };
    let inserted = Document {
        nodes: d1.nodes.update(parent as int, Node { children: kids, ..pn }).update(
            node as int,
            Node { parent: Some(parent), ..d1.nodes[node as int] },
        ),
    };
    // 7.4 to 7.6: slots; 7.7.1† "Run the insertion steps with
    // inclusiveDescendant."; 7.7.2 onward, 8 onward: custom elements,
    // observers, children changed and post-connection steps; not modelled
    // beyond the hook.
    insertion_steps(inserted, node)
}

/// DOM §4.2.3 "append" a node to a parent: "pre-insert node into parent
/// before null." "Pre-insert": "1. Ensure pre-insert validity given node,
/// parent, child" ([`insert_requires`]). "2. Let referenceChild be child.
/// 3. If referenceChild is node, then set referenceChild to node's next
/// sibling." (child is null.) "4. Insert node into parent before
/// referenceChild." "5. Return node."
pub open spec fn append(doc: Document, parent: NodeId, node: NodeId) -> Document {
    insert(doc, node, parent, None)
}

/// DOM §4.2.3 "pre-insert" `node` into `parent` before `child` (non-null).
/// Steps as [`append`]; step 3 does not apply (`child` is not `node`,
/// [`insert_requires`]).
pub open spec fn insert_before(doc: Document, parent: NodeId, node: NodeId, child: NodeId) -> Document {
    insert(doc, node, parent, Some(child))
}

/// `n` more children of `from`, moved in order to the end of `to`'s.
pub open spec fn reparent_children_n(doc: Document, from: NodeId, to: NodeId, n: nat) -> Document
    decreases n,
{
    if n == 0 || doc.nodes[from as int].children.len() == 0 {
        doc
    } else {
        reparent_children_n(append(doc, to, doc.nodes[from as int].children[0]), from, to, (n - 1) as nat)
    }
}

/// HTML §13.2.6.4.7 adoption agency, step 4.17: "Take all of the child
/// nodes of furthest block and append them to the element created in the
/// last step." Each child in order is appended (DOM "append"), which first
/// removes it from `from`; so the first remaining child is always the next.
pub open spec fn reparent_children(doc: Document, from: NodeId, to: NodeId) -> Document {
    reparent_children_n(doc, from, to, doc.nodes[from as int].children.len())
}

/// What the parser guarantees of [`reparent_children`]: two distinct nodes
/// of a well-formed arena that may have children, and `to` is not a
/// descendant of `from` (in the adoption agency, `to` is a new element).
pub open spec fn reparent_children_requires(doc: Document, from: NodeId, to: NodeId) -> bool {
    &&& wf(doc)
    &&& valid(doc, from)
    &&& valid(doc, to)
    &&& from != to
    &&& may_have_children(doc.nodes[from as int].kind)
    &&& may_have_children(doc.nodes[to as int].kind)
    &&& !is_inclusive_ancestor(doc, from, to)
}

// ---------------------------------------------------------------------
// Data and attributes

/// DOM §4.10 "replace data" of a `Text` node with offset = its length, count
/// 0 and `data`: "4. … Insert data into node's data after offset code
/// units." with nothing to delete (steps 5 to 6) and no live range to
/// update (steps 8 to 11, not modelled). The data is appended.
pub open spec fn append_data(doc: Document, n: NodeId, data: Seq<u32>) -> Document {
    let node = doc.nodes[n as int];
    let k = match node.kind {
        NodeKind::Text { data: old } => NodeKind::Text { data: old + data },
        other => other,
    };
    Document { nodes: doc.nodes.update(n as int, Node { kind: k, ..node }) }
}

/// DOM §4.9 "append an attribute" `attr` to element `e`: "1. Append
/// attribute to element's attribute list." Steps 2 and 3 set the
/// attribute's element and node document (implicit). Step 4, "handle
/// attribute changes", queues records and runs attribute change steps; not
/// modelled.
pub open spec fn append_attribute(doc: Document, e: NodeId, attr: Attr) -> Document {
    let node = doc.nodes[e as int];
    let k = match node.kind {
        NodeKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner } => NodeKind::Element {
            namespace,
            prefix,
            local_name,
            attributes: attributes.push(attr),
            template_contents,
            form_owner,
        },
        other => other,
    };
    Document { nodes: doc.nodes.update(e as int, Node { kind: k, ..node }) }
}

/// Set the document's mode (DOM §4.5; HTML §13.2.6.4.1 sets it).
pub open spec fn set_mode(doc: Document, mode: DocumentMode) -> Document {
    let node = doc.nodes[0];
    let k = match node.kind {
        NodeKind::Document { url, base_url, .. } => NodeKind::Document { mode, url, base_url },
        other => other,
    };
    Document { nodes: doc.nodes.update(0, Node { kind: k, ..node }) }
}

// ---------------------------------------------------------------------
// Phase 7 item 7.13: the mutation algorithms scripts call
//
// Everything below was transcribed from memory of the DOM Standard, not read
// at the pinned commit: its section and step numbers carry the mark †
// (docs/phases/phase-7.md's convention), and must be checked against the
// pinned snapshot before a review relies on them. The algorithms are
// §4.2.3 "ensure pre-insertion validity", "pre-insert", "insert" (for a
// DocumentFragment too), "replace", "replace all", §4.4 "clone a node" and
// §4.9 "change", "remove" and "replace an attribute".
//
// Modelling choices of this part, in addition to those at the top of the
// file:
// - **Errors are values.** "Throw a HierarchyRequestError / NotFoundError"
//   becomes returning `Some(DomError)` from an `_error` function; an
//   algorithm that throws leaves the tree unchanged, because every check
//   runs before the first change. A caller (Phase 7's bindings) turns the
//   value into a `DOMException`.
// - **A DocumentFragment may be inserted.** The restriction of
//   [`insert_requires`] (the node is not a fragment) belongs to the
//   parser's calls; [`insert_any`] below handles a fragment, as step 4 of
//   "insert" does. A fragment is still never a child (`wf`), so inserting
//   one moves its children and leaves it empty and parentless.
// - **The only `CharacterData` interfaces are `Text`, `Comment` and
//   `ProcessingInstruction`**, as the arena has no `CDATASection` (a
//   `Text` subclass, so "node is a Text node" would cover it).
// - **"Host-including inclusive ancestor"** (§4.2) is
//   [`is_host_including_inclusive_ancestor`]: walk parents to the root, and
//   from a fragment root that has a host continue at the host. The walk is
//   deterministic, so a node it reaches it reaches within `nodes.len()`
//   steps (it visits each node at most once before repeating), which is
//   the fuel.
// - **Index arguments.** An attribute is named by its position in the
//   element's attribute list (DOM names the `Attr` object); the position
//   is a precondition, as the attribute's presence in the list is.
// - **Attributes' "handle attribute changes"** (queues records, runs
//   attribute change steps) is not modelled, as in [`append_attribute`].
// - **Steps 5 and 6 are checked against a second statement.** The checks
//   of "ensure pre-insertion validity" and "replace" (their steps 5 and 6)
//   are written as DOM writes them. [`children_rules_hold`] says the same
//   thing as a property of the tree: only a document has a doctype child,
//   and a document's children have no `Text`, at most one element, at most
//   one doctype and no doctype after the element
//   ([`document_children_ok`]). `ops_lemmas`'s theorems prove, for a node
//   with no parent (a fragment never has one), that a call passes steps 5
//   and 6 exactly when the tree after the insertion obeys the rules.
//   (A node that has a parent is first removed from it by "adopt"; the
//   theorems do not cover that case, and DOM's checks count such a node
//   among its new parent's children, so they would refuse some calls the
//   rules allow.)
// - **Shallow "clone a node" only.** The clone children flag is never
//   set: a deep clone's recursion is not specified here (not done).
// - **A template** is an element whose template contents is non-null (the
//   parser creates the contents of every `template` it creates). Its clone
//   gets contents of its own (HTML §4.12.3 "when a template element is
//   created"); the copied element's form owner is null (a created element
//   has none).
// - **The node limit applies to clones** like to creation: a clone that
//   needs `k` new nodes is refused (the arena unchanged) unless the arena
//   can hold `k` more.
// - **The hooks** [`insertion_steps`] and [`removing_steps`] are called
//   from [`insert`] and [`remove`], so every algorithm below reaches them
//   through those two.
// ---------------------------------------------------------------------

/// The `DOMException` names the algorithms below throw.
pub enum DomError {
    /// "HierarchyRequestError"
    HierarchyRequest,
    /// "NotFoundError"
    NotFound,
}

/// The kinds of node the validity checks count among a parent's children.
pub enum NodeTag {
    /// An `Element`.
    Element,
    /// A `Text` node.
    Text,
    /// A `DocumentType` (a "doctype").
    DocumentType,
}

/// A node of kind `k` is a node of the tag `t`.
pub open spec fn has_tag(k: NodeKind, t: NodeTag) -> bool {
    match t {
        NodeTag::Element => k is Element,
        NodeTag::Text => k is Text,
        NodeTag::DocumentType => k is DocumentType,
    }
}

/// How many of `kids` have the tag `t`, other than `skip` (a node, or none).
/// Defined from the end, so that appending a child adds its share.
pub open spec fn count_tag(doc: Document, kids: Seq<NodeId>, t: NodeTag, skip: Option<NodeId>) -> nat
    decreases kids.len(),
{
    if kids.len() == 0 {
        0
    } else {
        let last = kids.last();
        count_tag(doc, kids.drop_last(), t, skip) + if has_tag(doc.nodes[last as int].kind, t) && skip != Some(last) {
            1nat
        } else {
            0nat
        }
    }
}

/// DOM §4.2 "next sibling": "the first following sibling", null if there is
/// none (or no parent).
pub open spec fn next_sibling(doc: Document, n: NodeId) -> Option<NodeId> {
    match parent(doc, n) {
        None => None,
        Some(p) => {
            let i = index_of(children(doc, p), n);
            if 0 <= i && i + 1 < children(doc, p).len() {
                Some(children(doc, p)[i + 1])
            } else {
                None
            }
        },
    }
}

/// `a` is `x` or one of its first `fuel` host-including ancestors (§4.2).
pub open spec fn host_including_within(doc: Document, a: NodeId, x: NodeId, fuel: nat) -> bool
    decreases fuel,
{
    if x == a {
        true
    } else if fuel == 0 {
        false
    } else {
        match parent(doc, x) {
            Some(p) => host_including_within(doc, a, p, (fuel - 1) as nat),
            None => match doc.nodes[x as int].kind {
                // x is a root: "if B's root has a non-null host and A is a
                // host-including inclusive ancestor of B's root's host".
                NodeKind::DocumentFragment { host: Some(h) } => host_including_within(doc, a, h, (fuel - 1) as nat),
                _ => false,
            },
        }
    }
}

/// DOM §4.2 "host-including inclusive ancestor": "An object A is a
/// host-including inclusive ancestor of an object B, if either A is an
/// inclusive ancestor of B, or if B's root has a non-null host and A is a
/// host-including inclusive ancestor of B's root's host."
pub open spec fn is_host_including_inclusive_ancestor(doc: Document, a: NodeId, x: NodeId) -> bool {
    host_including_within(doc, a, x, doc.nodes.len())
}

/// The statements of step 6 of "ensure pre-insertion validity"† about a
/// `parent` that is a document, switched on the interface `node`
/// implements. True means "throw a HierarchyRequestError".
pub open spec fn pre_insert_document_violation(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    let kids = children(doc, parent);
    // "child is non-null and a doctype is following child" and "an element
    // is preceding child": the siblings after / before child.
    let after = match child {
        Some(c) => count_tag(doc, kids.subrange(index_of(kids, c) + 1, kids.len() as int), NodeTag::DocumentType, None),
        None => 0,
    };
    let before = match child {
        Some(c) => count_tag(doc, kids.subrange(0, index_of(kids, c)), NodeTag::Element, None),
        None => 0,
    };
    let child_is_doctype = match child {
        Some(c) => doc.nodes[c as int].kind is DocumentType,
        None => false,
    };
    match doc.nodes[node as int].kind {
        // "DocumentFragment: If node has more than one element child or has
        // a Text node child. Otherwise, if node has one element child and
        // either parent has an element child, child is a doctype, or child
        // is non-null and a doctype is following child."
        NodeKind::DocumentFragment { .. } => {
            let elements = count_tag(doc, children(doc, node), NodeTag::Element, None);
            let texts = count_tag(doc, children(doc, node), NodeTag::Text, None);
            elements > 1 || texts > 0 || (elements == 1 && (count_tag(doc, kids, NodeTag::Element, None) > 0 || child_is_doctype
                || after > 0))
        },
        // "Element: parent has an element child, child is a doctype, or
        // child is non-null and a doctype is following child."
        NodeKind::Element { .. } => count_tag(doc, kids, NodeTag::Element, None) > 0 || child_is_doctype || after > 0,
        // "DocumentType: parent has a doctype child, child is non-null and
        // an element is preceding child, or child is null and parent has an
        // element child."
        NodeKind::DocumentType { .. } => count_tag(doc, kids, NodeTag::DocumentType, None) > 0 || before > 0 || (child is None
            && count_tag(doc, kids, NodeTag::Element, None) > 0),
        _ => false,
    }
}

/// DOM §4.2.3† "ensure pre-insertion validity" of `node` into `parent`
/// before `child`: the error the algorithm throws, or none.
/// "1. If parent is not a Document, DocumentFragment, or Element node,
/// then throw a "HierarchyRequestError" DOMException. 2. If node is a
/// host-including inclusive ancestor of parent, then throw a
/// "HierarchyRequestError". 3. If child is non-null and its parent is not
/// parent, then throw a "NotFoundError". 4. If node is not a
/// DocumentFragment, DocumentType, Element, or CharacterData node, then
/// throw a "HierarchyRequestError". 5. If either node is a Text node and
/// parent is a document, or node is a doctype and parent is not a
/// document, then throw a "HierarchyRequestError". 6. If parent is a
/// document, and any of the statements below, switched on the interface
/// node implements, are true, then throw a "HierarchyRequestError"."
pub open spec fn pre_insert_error(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Option<DomError> {
    // 1.
    if !may_have_children(doc.nodes[parent as int].kind) {
        Some(DomError::HierarchyRequest)
    }
    // 2.
    else if is_host_including_inclusive_ancestor(doc, node, parent) {
        Some(DomError::HierarchyRequest)
    }
    // 3.
    else if child is Some && doc.nodes[child->Some_0 as int].parent != Some(parent) {
        Some(DomError::NotFound)
    }
    // 4. (Every kind but a Document is one of the listed.)
    else if doc.nodes[node as int].kind is Document {
        Some(DomError::HierarchyRequest)
    }
    // 5.
    else if (doc.nodes[node as int].kind is Text && doc.nodes[parent as int].kind is Document) || (doc.nodes[node as int].kind is DocumentType
        && !(doc.nodes[parent as int].kind is Document)) {
        Some(DomError::HierarchyRequest)
    }
    // 6.
    else if doc.nodes[parent as int].kind is Document && pre_insert_document_violation(doc, node, parent, child) {
        Some(DomError::HierarchyRequest)
    } else {
        None
    }
}

/// What the callers of the algorithms below guarantee of their ids: they
/// name nodes of a well-formed arena.
pub open spec fn ids_requires(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& wf(doc)
    &&& valid(doc, node)
    &&& valid(doc, parent)
    &&& match child {
        None => true,
        Some(c) => valid(doc, c),
    }
}

/// DOM §4.2.3 "remove" every child of `parent`, "in tree order": the
/// first `n` remaining children are removed, one after the other.
pub open spec fn remove_children_n(doc: Document, parent: NodeId, n: nat) -> Document
    decreases n,
{
    if n == 0 || children(doc, parent).len() == 0 {
        doc
    } else {
        remove_children_n(remove(doc, children(doc, parent)[0]), parent, (n - 1) as nat)
    }
}

/// "Remove all parent's children, in tree order" (DOM §4.2.3† "replace
/// all" step 5, "insert" step 4.1).
pub open spec fn remove_children(doc: Document, parent: NodeId) -> Document {
    remove_children_n(doc, parent, children(doc, parent).len())
}

/// Insert each of `nodes`, in order, into `parent` before `child` (DOM
/// §4.2.3 "insert" step 7, "For each node in nodes, in tree order"), each
/// a node that is not a `DocumentFragment`.
pub open spec fn insert_list(doc: Document, nodes: Seq<NodeId>, parent: NodeId, child: Option<NodeId>) -> Document
    decreases nodes.len(),
{
    if nodes.len() == 0 {
        doc
    } else {
        insert_list(insert(doc, nodes[0], parent, child), nodes.drop_first(), parent, child)
    }
}

/// DOM §4.2.3 "insert" a `DocumentFragment` `node` into `parent` before
/// `child` (null: `None`): "1. Let nodes be node's children, if node is a
/// DocumentFragment node; otherwise « node ». 2. Let count be nodes's size.
/// 3. If count is 0, then return. 4. If node is a DocumentFragment node:
/// 1. Remove its children with the suppress observers flag set. 2. Queue a
/// tree mutation record for node with « », nodes, null, and null." (not
/// modelled) "5. If child is non-null: …" (live ranges, not modelled) "6.
/// Let previousSibling be …" (observers, not modelled) "7. For each node
/// in nodes, in tree order: …" ([`insert_list`]; each node has no parent,
/// so step 7.1's adopt changes nothing).
pub open spec fn insert_fragment(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Document {
    // 1. and 2.
    let nodes = children(doc, node);
    // 3.
    if nodes.len() == 0 {
        doc
    } else {
        // 4.1
        let d1 = remove_children(doc, node);
        // 7.
        insert_list(d1, nodes, parent, child)
    }
}

/// DOM §4.2.3 "insert" for any `node`: a `DocumentFragment` by
/// [`insert_fragment`], any other node by [`insert`] (the parser's
/// operation, whose steps 1 to 4 do nothing for « node »).
pub open spec fn insert_any(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Document {
    if doc.nodes[node as int].kind is DocumentFragment {
        insert_fragment(doc, node, parent, child)
    } else {
        insert(doc, node, parent, child)
    }
}

/// DOM §4.2.3† "pre-insert" `node` into `parent` before `child`, on a
/// valid call: "1. Ensure pre-insertion validity of node, parent, and
/// child." (An error leaves the tree as it is: [`pre_insert_error`].) "2.
/// Let referenceChild be child. 3. If referenceChild is node, then set
/// referenceChild to node's next sibling. 4. Insert node into parent before
/// referenceChild. 5. Return node."
pub open spec fn pre_insert(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Document {
    // 1.
    if pre_insert_error(doc, node, parent, child) is Some {
        doc
    } else {
        // 2. and 3.
        let reference_child = if child == Some(node) {
            next_sibling(doc, node)
        } else {
            child
        };
        // 4.
        insert_any(doc, node, parent, reference_child)
    }
}

/// The statements of step 6 of "replace"† about a `parent` that is a
/// document; true means "throw a HierarchyRequestError". They differ from
/// pre-insert's: "an element child that is not child", and a doctype
/// following (or an element preceding) `child`.
pub open spec fn replace_document_violation(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> bool {
    let kids = children(doc, parent);
    let i = index_of(kids, child);
    let after = count_tag(doc, kids.subrange(i + 1, kids.len() as int), NodeTag::DocumentType, None);
    let before = count_tag(doc, kids.subrange(0, i), NodeTag::Element, None);
    match doc.nodes[node as int].kind {
        // "DocumentFragment: If node has more than one element child or has
        // a Text node child. Otherwise, if node has one element child and
        // either parent has an element child that is not child or a doctype
        // is following child."
        NodeKind::DocumentFragment { .. } => {
            let elements = count_tag(doc, children(doc, node), NodeTag::Element, None);
            let texts = count_tag(doc, children(doc, node), NodeTag::Text, None);
            elements > 1 || texts > 0 || (elements == 1 && (count_tag(doc, kids, NodeTag::Element, Some(child)) > 0 || after > 0))
        },
        // "Element: parent has an element child that is not child or a
        // doctype is following child."
        NodeKind::Element { .. } => count_tag(doc, kids, NodeTag::Element, Some(child)) > 0 || after > 0,
        // "DocumentType: parent has a doctype child that is not child, or
        // an element is preceding child."
        NodeKind::DocumentType { .. } => count_tag(doc, kids, NodeTag::DocumentType, Some(child)) > 0 || before > 0,
        _ => false,
    }
}

/// Steps 1 to 6 of DOM §4.2.3† "replace" `child` with `node` within
/// `parent`: the error it throws, or none. "1. If parent is not a
/// Document, DocumentFragment, or Element node, then throw a
/// "HierarchyRequestError". 2. If node is a host-including inclusive
/// ancestor of parent, then throw a "HierarchyRequestError". 3. If child's
/// parent is not parent, then throw a "NotFoundError". 4. If node is not a
/// DocumentFragment, DocumentType, Element, or CharacterData node, then
/// throw a "HierarchyRequestError". 5. If either node is a Text node and
/// parent is a document, or node is a doctype and parent is not a
/// document, then throw a "HierarchyRequestError". 6. If parent is a
/// document, and any of the statements below, switched on the interface
/// node implements, are true, then throw a "HierarchyRequestError"."
pub open spec fn replace_error(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> Option<DomError> {
    // 1.
    if !may_have_children(doc.nodes[parent as int].kind) {
        Some(DomError::HierarchyRequest)
    }
    // 2.
    else if is_host_including_inclusive_ancestor(doc, node, parent) {
        Some(DomError::HierarchyRequest)
    }
    // 3.
    else if doc.nodes[child as int].parent != Some(parent) {
        Some(DomError::NotFound)
    }
    // 4.
    else if doc.nodes[node as int].kind is Document {
        Some(DomError::HierarchyRequest)
    }
    // 5.
    else if (doc.nodes[node as int].kind is Text && doc.nodes[parent as int].kind is Document) || (doc.nodes[node as int].kind is DocumentType
        && !(doc.nodes[parent as int].kind is Document)) {
        Some(DomError::HierarchyRequest)
    }
    // 6.
    else if doc.nodes[parent as int].kind is Document && replace_document_violation(doc, child, node, parent) {
        Some(DomError::HierarchyRequest)
    } else {
        None
    }
}

/// DOM §4.2.3† "replace" `child` with `node` within `parent`, on a valid
/// call. "7. Let referenceChild be child's next sibling. 8. If
/// referenceChild is node, then set referenceChild to node's next sibling.
/// 9. Let previousSibling be child's previous sibling. 10. Let
/// removedNodes be the empty set. 11. If child's parent is non-null, then:
/// 1. Set removedNodes to « child ». 2. Remove child with the suppress
/// observers flag set. 12. Let nodes be node's children if node is a
/// DocumentFragment node; otherwise « node ». 13. Insert node into parent
/// before referenceChild with the suppress observers flag set. 14. Queue a
/// tree mutation record … 15. Return child." Steps 9, 10, 12 (only
/// `nodes`' size matters to "insert") and 14 touch observers only. An
/// error (steps 1 to 6) leaves the tree as it is.
pub open spec fn replace(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> Document {
    if replace_error(doc, child, node, parent) is Some {
        doc
    } else {
        // 7.
        let reference0 = next_sibling(doc, child);
        // 8.
        let reference_child = if reference0 == Some(node) {
            next_sibling(doc, node)
        } else {
            reference0
        };
        // 11.
        let d1 = if doc.nodes[child as int].parent is Some {
            remove(doc, child)
        } else {
            doc
        };
        // 13.
        insert_any(d1, node, parent, reference_child)
    }
}

/// What a caller of [`replace_all`] guarantees: `parent` may have children,
/// `node` (if any) is not a document and not a host-including inclusive
/// ancestor of `parent`. (The standard's callers, `textContent` and
/// `replaceChildren`, have established what "insert" needs; DOM's "replace
/// all" checks nothing itself.)
pub open spec fn replace_all_requires(doc: Document, node: Option<NodeId>, parent: NodeId) -> bool {
    &&& wf(doc)
    &&& valid(doc, parent)
    &&& may_have_children(doc.nodes[parent as int].kind)
    &&& match node {
        None => true,
        Some(n) => valid(doc, n) && !(doc.nodes[n as int].kind is Document) && !is_host_including_inclusive_ancestor(doc, n, parent),
    }
}

/// DOM §4.2.3† "replace all with a node `node` within a node `parent`":
/// "1. Let removedNodes be parent's children. 2. Let addedNodes be the
/// empty set. 3. If node is a DocumentFragment node, then set addedNodes to
/// node's children. 4. Otherwise, if node is non-null, set addedNodes to «
/// node ». 5. Remove all parent's children, in tree order, with the
/// suppress observers flag set. 6. If node is non-null, then insert node
/// into parent before null with the suppress observers flag set. 7. If
/// either addedNodes or removedNodes is not empty, then queue a tree
/// mutation record for parent with addedNodes, removedNodes, null, and
/// null." Steps 1 to 4 and 7 only feed observers.
pub open spec fn replace_all(doc: Document, node: Option<NodeId>, parent: NodeId) -> Document {
    // 5.
    let d1 = remove_children(doc, parent);
    // 6.
    match node {
        Some(n) => insert_any(d1, n, parent, None),
        None => d1,
    }
}

// ---------------------------------------------------------------------
// Cloning (DOM §4.4† "clone a node")

/// The kind of the copy made by steps 2 and 3 of "clone a node"†: "2. If
/// node is an element, then: create an element with … node's local name,
/// node's namespace, node's namespace prefix …. Let copy be the result.
/// Then, for each attribute in node's attribute list: Let copyAttribute be
/// a clone of attribute. Append copyAttribute to copy. 3. Otherwise, let
/// copy be a node that implements the same interfaces as node, and
/// fulfills these additional requirements, switching on the interface node
/// implements: … DocumentType: Set copy's name, public ID, and system ID to
/// those of node. … Text, Comment: Set copy's data to that of node.
/// ProcessingInstruction: Set copy's target and data to those of node. Any
/// other node: Do nothing." A created element has no template contents
/// (yet) and no form owner. A document is not cloned here (one per arena).
pub open spec fn clone_kind(k: NodeKind) -> NodeKind {
    match k {
        NodeKind::Element { namespace, prefix, local_name, attributes, .. } => NodeKind::Element {
            namespace,
            prefix,
            local_name,
            attributes,
            template_contents: None,
            form_owner: None,
        },
        NodeKind::DocumentFragment { .. } => NodeKind::DocumentFragment { host: None },
        other => other,
    }
}

/// A template element (see the modelling choices).
pub open spec fn is_template(k: NodeKind) -> bool {
    k is Element && k->Element_template_contents is Some
}

/// How many nodes cloning `node` creates: the copy, and for a template its
/// contents too.
pub open spec fn clone_count(doc: Document, node: NodeId) -> nat {
    if is_template(doc.nodes[node as int].kind) {
        2
    } else {
        1
    }
}

/// DOM §4.4† "clone a node" `node`, with the clone children flag unset:
/// "1. If document is not given, let document be node's node document."
/// (One document.) "2.", "3." ([`clone_kind`]). "4. Set copy's node
/// document and document to document." (Implicit.) "5. Run any cloning
/// steps defined for node in other applicable specifications and pass copy,
/// node, document, and the clone children flag if set, as parameters."
/// (HTML §4.12.3: a template's cloning steps return when the flag is
/// unset; its copy was created with template contents, step 2.) "6. If the
/// clone children flag is set, …" (never.) "7. Return copy." The copy's id
/// is the next one; a template's contents' is the one after.
pub open spec fn clone_node(doc: Document, node: NodeId) -> (Document, NodeId) {
    // 2. and 3.
    let (d1, copy) = create_node(doc, clone_kind(doc.nodes[node as int].kind));
    // 5.
    if is_template(doc.nodes[node as int].kind) {
        (create_template_contents(d1, copy).0, copy)
    } else {
        (d1, copy)
    }
}

/// What the caller of [`clone_node`] guarantees: `node` is a node of a
/// well-formed arena, and not its document.
pub open spec fn clone_requires(doc: Document, node: NodeId) -> bool {
    &&& wf(doc)
    &&& valid(doc, node)
    &&& !(doc.nodes[node as int].kind is Document)
}

// ---------------------------------------------------------------------
// Attribute changes (DOM §4.9†)

/// The element `e` with its attribute list replaced by `attrs`.
pub open spec fn set_attributes(doc: Document, e: NodeId, attrs: Seq<Attr>) -> Document {
    let node = doc.nodes[e as int];
    let k = match node.kind {
        NodeKind::Element { namespace, prefix, local_name, template_contents, form_owner, .. } => NodeKind::Element {
            namespace,
            prefix,
            local_name,
            attributes: attrs,
            template_contents,
            form_owner,
        },
        other => other,
    };
    Document { nodes: doc.nodes.update(e as int, Node { kind: k, ..node }) }
}

/// DOM §4.9† "change an attribute" (the `i`th of `e`'s attribute list) "to
/// value": "1. Let oldValue be attribute's value. 2. Set attribute's value
/// to value. 3. Handle attribute changes for attribute with attribute's
/// element, oldValue, and value." (Not modelled.)
pub open spec fn change_attribute(doc: Document, e: NodeId, i: nat, value: Seq<u32>) -> Document {
    let attrs = doc.nodes[e as int].kind->Element_attributes;
    set_attributes(doc, e, attrs.update(i as int, Attr { value, ..attrs[i as int] }))
}

/// DOM §4.9† "remove an attribute" (the `i`th of `e`'s attribute list):
/// "1. Let element be attribute's element. 2. Remove attribute from
/// element's attribute list. 3. Set attribute's element to null. 4. Handle
/// attribute changes for attribute with element, attribute's value, and
/// null." (Step 3 is implicit, step 4 not modelled.)
pub open spec fn remove_attribute(doc: Document, e: NodeId, i: nat) -> Document {
    set_attributes(doc, e, doc.nodes[e as int].kind->Element_attributes.remove(i as int))
}

/// DOM §4.9† "replace an attribute" (the `i`th of `e`'s attribute list,
/// oldAttr) "with newAttr": "1. Replace oldAttr by newAttr in oldAttr's
/// element's attribute list. 2. Set newAttr's element to oldAttr's
/// element. 3. Set newAttr's node document to element's node document. 4.
/// Set oldAttr's element to null. 5. Handle attribute changes for oldAttr
/// with oldAttr's element, oldAttr's value, and newAttr's value." (Steps 2
/// to 4 are implicit, step 5 not modelled.)
pub open spec fn replace_attribute(doc: Document, e: NodeId, i: nat, new_attr: Attr) -> Document {
    set_attributes(doc, e, doc.nodes[e as int].kind->Element_attributes.update(i as int, new_attr))
}

/// What the callers of the attribute changes above guarantee: `e` is an
/// element of a well-formed arena and `i` names one of its attributes.
pub open spec fn attribute_requires(doc: Document, e: NodeId, i: nat) -> bool {
    &&& wf(doc)
    &&& valid(doc, e)
    &&& doc.nodes[e as int].kind is Element
    &&& i < doc.nodes[e as int].kind->Element_attributes.len()
}

// ---------------------------------------------------------------------
// The children rules, stated on their own (DOM §4.2.3† "ensure
// pre-insertion validity" steps 5 and 6, "replace" steps 5 and 6)

/// The rules a document's children obey (DOM §4.2.3† steps 5 and 6 of
/// "ensure pre-insertion validity" keep them true), stated about the
/// sequence itself, not as checks on an insertion: no `Text` node, at
/// most one element, at most one doctype, and the doctype is not after the
/// element. (Comments and processing instructions may be anywhere.)
pub open spec fn document_children_ok(doc: Document, kids: Seq<NodeId>) -> bool {
    &&& forall|j: int| 0 <= j < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is Text)
    &&& forall|j: int, k: int| 0 <= j < k < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is Element
        && doc.nodes[#[trigger] kids[k] as int].kind is Element)
    &&& forall|j: int, k: int| 0 <= j < k < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is DocumentType
        && doc.nodes[#[trigger] kids[k] as int].kind is DocumentType)
    &&& forall|j: int, k: int| 0 <= j < k < kids.len() ==> !(doc.nodes[#[trigger] kids[j] as int].kind is Element
        && doc.nodes[#[trigger] kids[k] as int].kind is DocumentType)
}

/// The children rules hold in the whole arena: only a document has a
/// doctype child (step 5: "node is a doctype and parent is not a
/// document"), and the document node's children obey
/// [`document_children_ok`] (step 6). The document node, `nodes[0]`, is the
/// only document ([`wf`]).
pub open spec fn children_rules_hold(doc: Document) -> bool {
    &&& forall|p: int, j: int| 0 <= p < doc.nodes.len() && !(doc.nodes[p].kind is Document) && 0 <= j < doc.nodes[p].children.len()
        ==> !(doc.nodes[#[trigger] doc.nodes[p].children[j] as int].kind is DocumentType)
    &&& 1 <= doc.nodes.len() && document_children_ok(doc, doc.nodes[0].children)
}

} // verus!
