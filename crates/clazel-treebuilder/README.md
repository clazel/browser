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
  The tokenizer is a parameter of the spec (`TokFns`); `exec::driver`
  runs `clazel-html`'s tokenizer through the executable step. "Get an
  encoding" and "extract a character encoding from a meta element" are
  parameters too.

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
  parser. `theorem_reachable_stopped`: every reachable parser that has
  stopped has an empty stack and satisfies `modes_ok` too (a rule that
  stops part-way has popped the stack, and the helpers after the stop
  keep the modes), so every reachable parser satisfies `modes_ok`.
- **Proven, the document** (`src/theorems/`): `theorem_doc_wf` and
  `theorem_open_elements_in_doc` (a step keeps the DOM well formed and
  every id of the parse state in the document) and
  `theorem_nodes_per_token` (one token creates at most 44 + 6T + 2F +
  P(F + 1) nodes), for a step from a parser with `parser_wf`, a valid head
  pointer and `dispatch_needs` (which `reachable_inv` gives); the last
  also assumes no element has two formatting entries, and keeps that.
  `theorem_open_distinct`: under the same hypotheses, a step keeps the
  elements of the stack of open elements distinct (every element pushed
  is new; "after head" pushes the `head` element back and removes that
  last entry again).
  `theorem_reachable_wf` discharges these hypotheses: every parser
  reachable from `new_parser` or `fragment_parser`, stopped or not, has
  `parser_wf` (a well-formed document, every id of its parse state in the
  document, `modes_ok`), no element with two formatting entries, distinct
  elements on the stack (an empty one once stopped), only HTML elements
  in the list of active formatting elements, the fragment case's
  redirection map (or none), and, until it stops, a valid head pointer (a
  `head` start tag the node limit stops leaves the pointer at the
  Document). `theorem_reachable_parser_inv`: every reachable parser
  satisfies `parser_inv` until it stops, `templates_wf` included (every
  `template` record on the stack has template contents, and no
  `template` element without them has a child: the reachable-state
  invariant carries these document facts, `reachable::doc::dinv`, since
  every insertion's parent comes from the stack's tagged records). So
  `theorem_reachable_doc_wf`,
  `theorem_reachable_open_elements_in_doc` and
  `theorem_reachable_nodes_per_token` state the three for a step from
  every reachable parser, with no hypotheses. `theorem_reachable_w3c_facts`
  proves of every reachable parser the state preconditions of the W3C
  equivalence lemmas that are facts of reachable states
  (`document_rooted`, `no_document_redirect`, and until it stops
  `aa_wf`, `tags_wf`, distinct elements on the stack and, after "before
  html", `place_stable`, also with the `head` element pushed, and
  `html_only_at_root`; in "in cell", a `td` or `th` element in table
  scope), and `theorem_reachable_foreign_content` states the foreign
  content equivalence for every reachable parser and every token the
  tokenizer emits, with only the inputs where the two texts differ
  excluded. `theorem_reachable_frameset_cell` states the "in frameset"
  and "in cell" equivalences for every reachable parser and every token
  the tokenizer emits, with no hypothesis (the texts differ on no input a
  reachable parser meets). The facts behind them are part of
  `reachable_inv`: the root is the stack's only `html` element, and in
  "in cell" no `table` or `template` element is above the last cell.
- **Proven, actions** (`src/theorems/`): `theorem_actions_ordered`: over a
  whole parse, `StopParsing` occurs at most once and last, and
  `ChangeEncoding` at most once (never if the confidence starts certain),
  so the pipeline runs the parser at most twice. No hypotheses.
- **Proven, implementation** (`src/exec/`): every helper and every
  insertion mode's executable function equals its spec function and keeps
  the parse state invariant; `exec::step::step` equals `dispatch` on every
  state with `parser_inv` and `reachable_inv`, and keeps both. No recursion on
  the tree's depth or the input's length.
- **Proven, the driver** (`src/exec/driver.rs`): `parse_real` and
  `parse_fragment_real` equal the spec's `parse` and `parse_fragment`
  with `TokFns` instantiated by `clazel-html`'s tokenizer
  (`spec::base::join::join_fns`, from `join_start`, over the preprocessed
  input): for some `n`, every bound `m >= n` on the tokens gives the
  driver's document (fragment) and actions
  (`contract::parse_real_ensures`, `contract::parse_fragment_real_ensures`),
  and the parser has stopped. `join_fns` queues the tokens one tokenizer
  step emits and hands them out one at a time, applying the step's switch
  and the foreign-content flag after each, as the driver does; after the
  tokenizer stops it gives end-of-file. `theorem_eof_stops`: the step on
  an end-of-file token stops the parser, from every parser (no
  hypotheses), so the driver's loop ends.
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
  (`tests/data/wpt-tree-construction/`, pinned WPT commit), through
  `clazel-html`'s proven tokenizer and the proven step, joined by
  `exec::driver` (`parse_real`, `parse_fragment_real`: it feeds each token
  to `step` and applies the step's tokenizer switches and the
  foreign-content flag before the next; proven equal to the spec's
  `parse` and `parse_fragment` with that tokenizer, so these are results
  of the spec), the tree printed in the suite's format
  and compared byte for byte: 1,963 of 1,967 pass, and the 4 expected
  failures are the `selectedcontent` restriction above (`webkit02.dat` 44
  to 47); the 6 `scripted_*.dat` cases need a script engine and are not
  run. Cases with neither `#script-on` nor `#script-off` run with
  scripting off only.
- **Differential** (`tests/conformance_html5ever.rs`): Servo's `html5ever`
  0.39.0, with `markup5ever_rcdom` for its tree (test-only, 22 packages),
  against the same driver, both trees printed in the suite's format and
  compared byte for byte. On the suite's inputs (3,898 parses: a case
  naming no scripting flag runs with both) 3,699 agree and 199 differ, each
  in a listed class with a rule over the input, and in every one ours is
  the suite's expected tree: processing instructions (175; html5ever
  predates them and makes bogus comments), `search` in the special
  category (10), "after head" setting frameset-ok to "ok" (6), "parsing
  template contents" for `form` (6), and an `input` start tag in a `select`
  fragment, which html5ever inserts though the text it implements ignores
  it (2). On 10,000 random tag-soup inputs 9,991 agree and 9 differ by the
  same rules, one in a class seen only there: html5ever's "in table body"
  scope test omits `thead`, a bug visible in template contents. No failure
  and no bug in this crate; the `selectedcontent` cases above agree (both
  leave the element empty).

## Left

- Whether reachable parsers need the 6T term of the nodes-per-token bound.
  The term pays for "in template"'s end of file, which pops a template,
  resets the mode and reprocesses, once per template: the generic proof
  cannot exclude that each reset lands in a mode whose end of file
  creates implicit elements. On reachable parsers it does not seem to
  (the `body` element "after head" inserts is found by every later
  reset), but proving it needs invariants on the elements below each
  `template` on the stack, which nothing proves yet.
- The W3C "in body" equivalence's precondition `element_plain` of the
  `html` and `body` elements (their attributes have no namespace or
  prefix), a fact of reachable states not yet proven: it needs the
  attributes of document nodes tracked through every helper (the
  document theorems keep only namespaces and local names) and the
  tokens' attributes being plain carried through every rule application.
