# clazel-selectors

CSS selectors for Clazel's Phase 5 browser (item 5.5 of
[phase-5.md](../../docs/phases/phase-5.md)). Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

`src/spec.rs` transcribes Selectors Level 4 (pinned at a csswg-drafts commit) for the
item's subset: the grammar, type, universal, namespace, attribute, class and ID
selectors, `:link`/`:visited`/`:any-link`, the tree-structural pseudo-classes,
`:is()`/`:not()`/`:where()`, the four combinators, specificity and "match a selector
against an element", with HTML's case rules and CSSOM's serialization. Its modelling
choices are listed at its top.

What is proven, and what is not:

- **Matching** (`src/exec_match.rs`) runs the algorithm of `src/algorithm.rs` over a
  `clazel-dom` arena, through its public readers, and is proven equal to it;
  `theorem_match_total` proves the algorithm gives the spec's answer in every
  well-formed arena, within the work bound (compounds × the chain of ancestors, or ×
  those and their earlier siblings when a `+` or `~` is used).
- **Specificity** (`src/exec_specificity.rs`) is proven equal to §17.
- **Parsing** (`src/exec_parse.rs`) and **serialization** (`src/exec_serialize.rs`) are
  checked by Verus for panics, overflow and termination only. They are **not yet proven
  equal to the spec**; `src/contract.rs` states what they must meet. What matching needs
  of a parse is checked by `src/exec_check.rs`, which is proven, before the parser
  returns.
- Theorems about the spec, in `src/lemmas.rs`: `theorem_parse_total`,
  `theorem_match_total`, `theorem_specificity_monotone`, `theorem_where_zero` and
  `theorem_is_most_specific`.
- `mutations.json`: one mutation per simple selector, combinator, specificity rule and
  the quirks rule, and a few of the grammar's, each with a certificate in
  `src/examples.rs`.

`tests/conformance_selectors.rs` runs WPT's `css/selectors/parsing` (vendored in
`tests/data/`, with what it is in its `SOURCE.md`), listing each expected failure with
its reason, and checks matching and §17's specificity examples on small arenas.

Tier 0 for now: a tier also needs the parser and serializer proven, an independent
transcription, and the differential against Servo's `selectors`. The target is tier 2,
since this crate parses selectors that a page chose.
