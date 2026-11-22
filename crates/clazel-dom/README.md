# clazel-dom

The DOM node tree for the Clazel browser, as an arena: the tree the HTML
parser builds and every later phase reads. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

## What it is

- **The tree:** a document is a sequence of nodes indexed by id, node 0
  being the document. A node is a `Document` (mode, URL, base URL), a
  `DocumentType`, an `Element` (namespace, prefix, local name, attribute
  list, template contents, form owner), a `Text`, a `Comment`, a
  `ProcessingInstruction` or a `DocumentFragment` (host), with a parent, an
  ordered list of children and a wrapper slot for Phase 7. DOM §4.2, §4.4
  to §4.14 (the parts the parser uses), Infra §8's six namespaces, HTML
  §4.12.3 template contents.
- **Operations:** DOM §4.2.3 "insert", "append", "pre-insert" (before a
  child) and "remove", §4.5 "adopt", the adoption agency's "move all
  children" (`reparent_children`), node creation, template contents, §4.10
  "replace data" at the end of a `Text`, §4.9 "append an attribute", and
  setting the document's mode. Readers: parent, children, previous
  sibling, last child, "has a child", inclusive ancestor, kind.
- **Operations scripts call (Phase 7 item 7.13)**, specified and proven
  in the same way: DOM §4.2.3† "ensure pre-insertion validity"
  (`ensure_pre_insertion_validity`, returning the `HierarchyRequestError`
  or `NotFoundError` the standard throws), "pre-insert" (`pre_insert`, with
  a node or a `DocumentFragment`, before a child or at the end), "replace"
  (`replace`), "replace all" (`replace_all`), shallow "clone a node"
  (`clone_node`), "adopt" (`adopt`), and §4.9† "change", "remove" and
  "replace an attribute" (`change_attribute`, `remove_attribute`,
  `replace_attribute`). The named hooks "insertion steps" and "removing
  steps" are called from "insert" and "remove" and change nothing here.
  Section and step numbers marked † were written from memory, not read at
  the pinned DOM commit. Deep "clone a node" (`clone_deep`, the clone
  children flag) is specified as a relation (the copy is an isomorphic
  fresh subtree of the host-including subtree, template contents included)
  and implemented as a worklist, not a recursion. A clone that does not fit
  the node limit leaves the arena as it was, and is refused only if it does
  not fit: a successful clone adds exactly `subtree_size` nodes (a count of
  the host-including subtree, proven), and a refusal needs the arena to be
  unable to hold that many more. It requires a host-acyclic arena
  (`host_acyclic`): `wf` forbids a cycle of parents but not one through a
  template's host, whose unfolding is infinite. Every operation keeps
  `host_acyclic` (`src/host_acyclic_lemmas.rs`), so it is an invariant of
  the tree and a caller that starts from `new_document` has it for free;
  `wf` itself is not strengthened: the tree builder's raw inserts would
  then each need the host half of the check proven. Document-children
  rules (step 6 of validity) and the Text/doctype rule (step 5) are covered
  by `tests/operations.rs` only: no theorem says them, so no mutation of
  them is certified.
- **A node limit**, 4,000,000 nodes: creation is refused beyond it, and the
  tree builder treats the refusal as "stop parsing". This is the one
  deliberate deviation from the standards, which have no limit.
- **Ids are stable:** "remove" detaches a node and keeps its record, and
  ids are never reused, so later phases can hold a node across its removal.

Out of scope, never modelled (none changes the tree, and none has an effect
without scripting): mutation observers, live ranges, `NodeIterator`s,
slots, shadow trees, custom element reactions, and the insertion, removing
and children changed steps. "Ensure pre-insert validity" is a precondition
the tree builder proves of its calls, not a check at run time.

## Verification

Tier 2 is declared (`tier = 2` in `Cargo.toml`); it becomes real only when
CI's full verification is green on the pull request that raised it
(`phase4/dom-conformance-tier2`): until then the list below is the evidence,
not the tier. The conformance evidence is the crate's own
`tests/conformance_dom.rs`, in addition to the tree-construction suite that
`clazel-treebuilder` runs through this arena.

- **Proven (`src/lemmas.rs`):** every operation keeps the tree well formed
  (`wf`): a child's parent lists it and conversely, children lists have no
  duplicates, only documents, elements and fragments have children, node 0
  is the only document and has no parent, a template's contents is a
  parentless fragment hosted by it, and the tree is acyclic, with a witness
  that is each node's chain of inclusive ancestors (so its length is the
  node's depth, one more than its parent's). Each operation also does what
  its DOM steps say: after "insert", the node's parent is the parent and it
  sits at the reference child's index, immediately before it; after
  "remove", the node has no parent and is gone from its parent's children;
  `reparent_children` moves all children in order. `remove` changes only
  the node's parent and its parent's children, and no operation shrinks the
  arena or changes an existing node's kind except its own target
  (`theorem_remove_keeps_record`, `theorem_ids_stable`). What template
  contents, "append an attribute" and setting the mode leave alone, and
  that "remove" keeps the siblings' order, are theorems of their own
  (`theorem_*_frame`, `theorem_remove_keeps_order`), so that proofs needing
  only well-formedness do not carry them. The twenty-six theorems are listed
  in `Cargo.toml` (nine of them, in `src/ops_lemmas.rs`, are Phase 7
  item 7.13's).
- **Proven (`src/host_acyclic_lemmas.rs`):** every operation keeps
  `host_acyclic`, the one thing `wf` does not say (no cycle through a
  template's host): creating a node or template contents, attribute and
  mode changes, `remove`, `adopt`, pre-insert, replace, replace all, shallow
  and deep clone. Pre-insert, replace and replace all need nothing but
  `host_acyclic` of their input: DOM's "host-including inclusive ancestor"
  check (step 2 of validity) is what refuses a cycle. The raw `insert`,
  `append`, `insert_before` and `reparent_children`, which the parser calls
  after its own checks, carry only the inclusive-ancestor half of that
  check, which is not enough (a template inserted below a node of its own
  contents passes it), so they additionally need `parent` not to be below
  `node` through hosts (`host_acyclic_contract::insert_acyclic_requires`,
  `host_acyclic_contract::reparent_children_acyclic_requires`).
- **Proven (`src/exec.rs`):** the executable arena equals the spec, for
  every operation and reader (the contracts are `src/contract.rs`). It is
  safe Rust with no recursion; a node's children are edited in place, and
  `reparent_children` is linear in the number of moved children.
- **Independent transcription:** `independent.rs` transcribes DOM "insert",
  "adopt" and "remove" again from the standard's text, and
  `independent_equivalence.rs` proves them equal to the spec on the parser's
  calls. DOM §4.2.3 has no second source, so this is a same-text
  transcription: it catches slips, not a shared misreading.
- **Mutations:** twenty-six deliberately broken specs (twelve of them for
  item 7.13's operations, `src/ops_mutation_lemmas.rs`: validity steps 1 to
  4 skipped, replace not removing, replace all keeping the old children, a
  fragment's first child dropped, a clone without attributes or with the
  wrong count, and the three attribute changes), the first fourteen being a parent pointer not
  set, a child inserted at the wrong index, `remove` leaving the child
  listed or rotating the siblings, `reparent_children` reversing the order,
  the limit off by one, `set_mode` swapping the URLs, `append_attribute`
  prepending, template contents clearing the form owner, `adopt` not
  detaching, `previous_sibling` and `last_child` wrong, `append_data`
  prepending, fragments unable to hold children), each rejected by a
  certificate Verus checks (`mutations.json`). Not covered, because a
  certificate cannot evaluate `wf` (an existential): dropped clauses of
  `wf_with`, and of `insert_requires` and `reparent_children_requires`
  (both start with `wf(doc)`).
- **Conformance (`tests/conformance_dom.rs`)**, two suites, each reported
  by a `clazel-conformance:` line (counts from the last local run):
  - *html5lib tree shapes (WPT)*, 1,967 of 1,967 cases: **not a
    tree-construction test** (no HTML is parsed). Every expected tree of the
    vendored suite (the table generated for `clazel-treebuilder`, shared by
    `include!`, not copied) is read by the test's own reader of the suite's
    text format into an arena using only the arena's own operations (create,
    template contents, append, append attribute), re-checked clause by
    clause for the executable statement of `wf` through the readers,
    printed again by a walk over `children` and `kind` and compared byte for
    byte with the original text; that first step is close to a round trip.
    What gives the suite teeth is that the same tree is then built four more
    ways (a control copy with `append`; inserting the children last to first
    with `insert_before`; building under a scratch parent and moving with
    `reparent_children`; appending and then removing and re-inserting every
    child at its place), and the original has every node removed and
    re-inserted in place: each must print the same text, pass the `wf`
    check, and have the same node fields and attribute order. No expected
    failures.
  - *`markup5ever_rcdom` 0.39.0 differential*, 3,000 of 3,000 random
    operation sequences of 40 operations (a seeded `SplitMix64`, no `rand`):
    create, append, insert-before, remove, moving a subtree (22,165 moves,
    18,492 to another parent, including into template contents),
    move-all-children, text appends, attributes and mode changes, applied to
    the arena and to an `RcDom` (elements in the HTML, SVG, MathML or null
    namespace with a prefix or none, attributes with namespaces and
    prefixes, doctypes with system ids), with whole trees (the document and
    every detached subtree; attributes in list order, prefixes and null
    namespaces shown) compared after every operation, together with the
    invariants the arena proves. The oracle is driven by detaching a node
    first (DOM "adopt"), because `RcDom`'s `append_before_sibling` computes
    its index before detaching (see the test's module doc).
  - Under Miri both suites run on a stride of their inputs, and the
    summary lines are not printed. Miri warns about an integer-to-pointer
    cast inside `tendril` (the oracle's string type), not in this crate.
- **Not proven:** that the spec transcribes the DOM Standard correctly
  beyond the above; the two suites and the independent transcription are
  the evidence. `tests/arena.rs` and `tests/operations.rs` hold ordinary unit tests. One restriction
  the tests respect and the spec leaves to the parser: inserting a template
  into its own contents is not excluded by `insert_requires` (DOM's
  host-including ancestor check), so the differential never makes that call.
- **Modelling choices** (listed at the top of `src/spec.rs`): one arena per
  document; ids are `usize` and never reused; template contents are held
  outside `children`; strings are code points; the operations take the
  parser's class of calls as preconditions.

## Trust

The proofs assume the Rust compiler, Verus and its solver, `vstd`, and that
the spec transcribes the standards correctly. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now).

```rust
use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;

let s = |t: &str| t.chars().map(u32::from).collect::<Vec<u32>>();
let mut doc = Arena::new(s("about:blank"));
let html = doc
    .create(ExecKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: s("html"),
        attributes: Vec::new(),
        template_contents: None,
        form_owner: None,
    })
    .unwrap_or_default();
doc.append(0, html);
assert_eq!(doc.children(0), &[html]);
assert_eq!(doc.parent(html), Some(0));
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
