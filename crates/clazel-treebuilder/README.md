# clazel-treebuilder

The HTML tree builder for the Clazel browser: HTML §13.2.6 tree
construction as a one-token step over a [`clazel-dom`](../clazel-dom/README.md)
arena. Part of [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs.

## What it is

- **Parse state** (HTML §13.2.4): the insertion mode, the stack of open
  elements, the list of active formatting elements with markers and the
  Noah's Ark clause, the head and form pointers, the flags, the stack of
  template insertion modes, and the scope algorithms.
- **Tree construction** (§13.2.6): the dispatcher, "creating and inserting
  nodes" (foster parenting, create an element for a token with its form
  owner, insert a character merging into `Text`), the 21 insertion modes of
  the pinned standard (it no longer has "in select" or "in select in
  table"), the adoption agency algorithm, foreign content with the three
  attribute adjustment tables and the SVG tag name table, and processing
  instructions.
- **The end** (§13.2.7) and **fragment parsing** (§13.4).
- **A transducer:** `dispatch(env, parser, token) -> (parser, actions)`,
  with `ChangeEncoding`, `ScriptReady` and `StopParsing` for the driver.
  The tokenizer is a parameter (`TokFns`), joined to `clazel-html` later;
  "get an encoding" and "extract a character encoding from a meta element"
  are parameters too.

Not modelled, each stated in `src/spec/mod.rs`: the sanitizer, declarative
shadow roots, template content patching, custom elements, scripting (the
parser pause flag is never set), parse errors, hooks outside §13.2 that run
when an element is popped (HTML §4.10.10's `selectedcontent` update), and a
node limit of 4,000,000 nodes (the parser stops parsing when it is reached).

## Verification

Tier 0 (target: tier 2). The proofs below go through locally; the tier
stays 0 until CI's full verification is green and the rest of tier 2's
evidence exists (see "Left" below).

- **Spec** (`src/spec/`): one spec function per insertion mode, its cases
  numbered in the standard's order, pinned to HTML commit `939677714d`.
- **Proven, termination** (`src/termination/`):
  `theorem_dispatch_total`: reprocessing a token always ends within
  `fuel_bound(parser)` rule applications, by a lexicographic ranking over
  the image token, the stack of template modes, a growth budget, the stack
  of open elements and an order of the rules, for every parser satisfying
  `modes_ok`.
- **Proven, reachable states** (`src/reachable/`): `theorem_reachable`:
  every parser reachable from `new_parser` or `fragment_parser` satisfies
  `reachable_inv` (each mode's stack shape, `modes_ok`, the cells of "in
  cell"), with no hypotheses; so reprocessing ends on every reachable
  parser.
- **Proven, the document** (`src/theorems/`): `theorem_doc_wf` and
  `theorem_open_elements_in_doc` (a step keeps the DOM well formed and
  every id of the parse state in the document) and
  `theorem_nodes_per_token` (one token creates at most 44 + 6T + 2F +
  P(F + 1) nodes), for a step from a parser with `parser_wf`, a valid head
  pointer and `dispatch_needs` (which `reachable_inv` gives); the last
  also assumes no element has two formatting entries. That every reachable
  parser has `parser_wf` is proven for the executable step, not yet at the
  spec level.
- **Proven, actions** (`src/theorems/`): `theorem_actions_ordered`: over a
  whole parse, `StopParsing` occurs at most once and last, and
  `ChangeEncoding` at most once (never if the confidence starts certain),
  so the pipeline runs the parser at most twice. No hypotheses.
- **Proven, implementation** (`src/exec/`): every helper and every
  insertion mode's executable function equals its spec function and keeps
  the parse state invariant; `exec::step::step` equals `dispatch` on every
  state with `parser_inv` and `reachable_inv`, and keeps both. No recursion on
  the tree's depth or the input's length.
- **Mutations** (`mutations.json`): 48; 22 killed by a theorem with a
  certificate Verus checks, 26 killed incidentally (they break only the
  implementation's proof: no theorem states the tree's shape, so the
  evidence for those is the conformance suite), 0 surviving.
- **Conformance** (`tests/conformance_tree_construction.rs`): the
  html5lib tree-construction suite as WPT keeps it
  (`tests/data/wpt-tree-construction/`, pinned WPT commit), through the
  executable parser, the tree printed in the suite's format and compared
  byte for byte. Until the join with `clazel-html`'s tokenizer, a test-only
  stand-in tokenizer runs the cases whose input it can tokenize exactly and
  refuses the rest (character references, processing instructions, CDATA,
  script data escapes, U+0000, …): 1,381 pass, 582 are refused by the
  stand-in, 4 are the `selectedcontent` restriction above; the 6
  `scripted_*.dat` cases need a script engine and are not run. Cases with
  neither `#script-on` nor `#script-off` run with scripting off only.

## Left

- The join with `clazel-html`'s tokenizer, and the full suite through it.
- The W3C HTML 5.2 §8.2.5 independent transcription (`independent.rs`).
- A differential against `html5ever` (22 packages with
  `markup5ever_rcdom`; not added).
- Spec-level `parser_wf` of every reachable parser, which would remove the
  hypotheses of `theorem_doc_wf`, `theorem_open_elements_in_doc` and
  `theorem_nodes_per_token`.
- Every mutation a certified kill (tier 2's requirement).
