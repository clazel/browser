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
  also assumes no element has two formatting entries, and keeps that.
  `theorem_reachable_wf` discharges these hypotheses: every parser
  reachable from `new_parser` or `fragment_parser` has a well-formed
  document, every id of its parse state in the document and no element
  with two formatting entries, and, until it stops, `parser_wf` and a
  valid head pointer. So `theorem_reachable_doc_wf`,
  `theorem_reachable_open_elements_in_doc` and
  `theorem_reachable_nodes_per_token` state the three for a step from
  every reachable parser, with no hypotheses.
- **Proven, actions** (`src/theorems/`): `theorem_actions_ordered`: over a
  whole parse, `StopParsing` occurs at most once and last, and
  `ChangeEncoding` at most once (never if the confidence starts certain),
  so the pipeline runs the parser at most twice. No hypotheses.
- **Proven, implementation** (`src/exec/`): every helper and every
  insertion mode's executable function equals its spec function and keeps
  the parse state invariant; `exec::step::step` equals `dispatch` on every
  state with `parser_inv` and `reachable_inv`, and keeps both. No recursion on
  the tree's depth or the input's length.
- **Independent transcription** (`src/independent/`): W3C HTML 5.2
  §8.2.5 (Recommendation, 14 December 2017), written without reading
  `src/spec/modes/`, proven equal to the spec for 21 of its 23 insertion
  modes, the adoption agency algorithm included, and for §8.2.5.5's rules
  for foreign content with their three attribute adjustments and the SVG
  tag name table (the tables written without reading
  `src/spec/base/tables.rs`; they have the same rows), with every difference
  between the two texts stated in the lemma's precondition (no processing
  instructions in the W3C text; "after head" sets frameset-ok; "in cell"
  checks a cell is in scope where WHATWG asserts it; "in body"'s
  `hgroup`, `menu`, `search`, `keygen` and `select` tags and its other
  `select` steps; "parsing template contents" in the `form` entries; "in
  table"'s characters with a `template` current node; the adoption agency
  algorithm's insertions where the redirection map or the WHATWG's step
  4.21 checks make them differ; an empty pending table character list;
  the DOCTYPE lists are taken as agreeing, not proven, except at the
  certificate's input; in foreign content, the WHATWG's `menu` breakout
  start tag and `br` and `p` breakout end tags, the W3C's fragment case of
  the breakout entries, and the WHATWG adjusting only attributes with no
  namespace). The table scope and the push onto the list of active
  formatting elements (§8.2.3.2, §8.2.3.3), the rules for foreign content
  (§8.2.5.5) and their tables are transcribed too and proven equal to the
  spec's. The two lemmas
  for "in body" and "in table" also assume stated facts of reachable
  states (ids on the stack and in the list of active formatting elements
  name nodes, records are tagged, the list holds HTML elements); the
  foreign content lemma assumes a token the dispatcher sends there, a
  tagged start tag with plain attributes, and distinct elements on the
  stack. Not
  transcribed: the W3C's "in select" and "in select in table", which the
  living standard removed.
- **Mutations** (`mutations.json`): 48, all killed by a theorem with a
  certificate Verus checks (termination, the order of actions, and the
  W3C equivalences, foreign content and its tables among them); none is
  killed only incidentally and none survives. Where a mutated rule tests
  an `exists` (the DOCTYPE system identifier list, "in table text"'s
  whitespace test), which `compute_only` does not evaluate, the
  certificate's witness is the quantifier-free part of the test at the
  input and Z3 derives the contradiction; the spec is unchanged.
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
- A differential against `html5ever` (22 packages with
  `markup5ever_rcdom`; not added).
- Spec-level `modes_ok` of a stopped reachable parser (so `parser_wf` is
  proven of reachable parsers only until they stop; a stopped parser
  takes no further step), and spec-level `templates_wf` of reachable
  parsers (the rest of `parser_inv`, which the executable step keeps).
- Whether reachable parsers need the 6T term of the nodes-per-token bound.
- A proof that the stack of open elements holds distinct elements on
  every reachable parser, which the foreign content equivalence assumes.
