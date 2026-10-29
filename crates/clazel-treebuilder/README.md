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
- **Independent transcription** (`src/independent/`): W3C HTML 5.2
  §8.2.5 (Recommendation, 14 December 2017), written without reading
  `src/spec/modes/`, proven equal to the spec for 21 of its 23 insertion
  modes, the adoption agency algorithm included, with every difference
  between the two texts stated in the lemma's precondition (no processing
  instructions in the W3C text; "after head" sets frameset-ok; "in cell"
  checks a cell is in scope where WHATWG asserts it; "in body"'s
  `hgroup`, `menu`, `search`, `keygen` and `select` tags and its other
  `select` steps; "parsing template contents" in the `form` entries; "in
  table"'s characters with a `template` current node; the adoption agency
  algorithm's insertions where the redirection map or the WHATWG's step
  4.21 checks make them differ; an empty pending table character list;
  the DOCTYPE lists are taken as agreeing, not proven). The two lemmas
  for "in body" and "in table" also assume stated facts of reachable
  states (ids on the stack and in the list of active formatting elements
  name nodes, records are tagged, the list holds HTML elements). Not
  transcribed: the W3C's "in select" and "in select in table", which the
  living standard removed.
- **Mutations** (`mutations.json`): 48; 41 killed by a theorem with a
  certificate Verus checks (termination, the order of actions, and the
  W3C equivalences), 7 killed incidentally (they break only the
  implementation's proof), 0 surviving. Of the 7, four change algorithms
  both transcriptions share (`push_formatting`'s Noah's Ark clause, the
  table scope, the SVG tag name and foreign attribute tables), so no W3C
  equivalence can tell them apart; one is in foreign content, which is not
  transcribed; and two cannot be evaluated by a certificate: the
  DOCTYPE system identifier test and "in table text"'s whitespace test are
  `exists` quantifiers in the spec, which `compute_only` does not
  evaluate, so no witness reaching them evaluates in the mutant and on the
  real spec.
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
- Spec-level `parser_wf` of every reachable parser, which would remove the
  hypotheses of `theorem_doc_wf`, `theorem_open_elements_in_doc` and
  `theorem_nodes_per_token`.
- Every mutation a certified kill (tier 2's requirement): 7 are not
  (see "Mutations" above); they need a second transcription of the shared
  algorithms and tables, of foreign content, or quantifier-free tests.
