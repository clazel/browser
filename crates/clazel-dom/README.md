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
  (`theorem_remove_keeps_record`, `theorem_ids_stable`). The thirteen
  theorems are listed in `Cargo.toml`.
- **Proven (`src/exec.rs`):** the executable arena equals the spec, for
  every operation and reader (the contracts are `src/contract.rs`). It is
  safe Rust with no recursion; a node's children are edited in place, and
  `reparent_children` is linear in the number of moved children.
- **Independent transcription:** `independent.rs` transcribes DOM "insert",
  "adopt" and "remove" again from the standard's text, and
  `independent_equivalence.rs` proves them equal to the spec on the parser's
  calls. DOM §4.2.3 has no second source, so this is a same-text
  transcription: it catches slips, not a shared misreading.
- **Mutations:** five deliberately broken specs (a parent pointer not set,
  a child inserted at the wrong index, `remove` leaving the child listed,
  `reparent_children` reversing the order, the limit off by one), each
  rejected by a certificate Verus checks (`mutations.json`).
- **Conformance (`tests/conformance_dom.rs`)**, two suites, each reported
  by a `clazel-conformance:` line (counts from the last local run):
  - *html5lib tree-construction trees (WPT)*, 1,967 of 1,967 cases: every
    expected tree of the vendored suite (the table generated for
    `clazel-treebuilder`, shared by `include!`, not copied) is read back
    into an arena using only the arena's own operations (create, template
    contents, append, append attribute), re-checked clause by clause for the
    executable statement of `wf` through the readers, printed again by a
    walk over `children` and `kind`, and compared byte for byte with the
    original text. No expected failures.
  - *`markup5ever_rcdom` 0.39.0 differential*, 3,000 of 3,000 random
    operation sequences of 40 operations (a seeded `SplitMix64`, no `rand`):
    create, append, insert-before, remove, moving a subtree (22,254 moves,
    18,664 to another parent, including into template contents),
    move-all-children, text appends, attributes and mode changes, applied to
    the arena and to an `RcDom`, with whole trees (the document and every
    detached subtree) compared after every operation, together with the
    invariants the arena proves. The oracle is driven by detaching a node
    first (DOM "adopt"), because `RcDom`'s `append_before_sibling` computes
    its index before detaching (see the test's module doc).
  - Under Miri both suites run on a stride of their inputs, and the
    summary lines are not printed. Miri warns about an integer-to-pointer
    cast inside `tendril` (the oracle's string type), not in this crate.
- **Not proven:** that the spec transcribes the DOM Standard correctly
  beyond the above; the two suites and the independent transcription are
  the evidence. `tests/arena.rs` holds ordinary unit tests. One restriction
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
