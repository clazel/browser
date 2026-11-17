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
  well-formed arena, and that the number of row entries it computes for one complex
  selector is at most compounds × the chain of ancestors (or × those and their earlier
  siblings when a `+` or `~` is used). That "work bound" counts only those row entries of
  the outer complex selector. It does **not** count the nested walks for the arguments of
  `:is()`, `:where()` and `:not()` (each is matched with its own run of the algorithm, and
  its work is dropped: `list_matches_exec` ignores it), the scans of an element's siblings
  for `:first-child`, `:nth-child()` and the other tree-structural pseudo-classes, nor the
  scans of its attributes and class words at each entry. Those costs are not bounded by
  any theorem here, and the first is not small: each row of a compound that holds
  `:is(...)` runs the argument's selector over the ancestors of the element the same way,
  so the work for an element at depth `d` with `k` levels of nesting is on the order of
  C(d + k, k). Measured in a debug build, `:is(` nested 6 deep on an element 40 deep took
  43 s. `MAX_NESTING` is 32. `tests/matching_through_parser.rs` has this as an ignored
  test that fails (`nested_functions_cost_too_much_on_a_deep_document`).
- **Specificity** (`src/exec_specificity.rs`) is proven equal to §17.
- **Serialization** (`src/exec_serialize.rs`) is proven equal to CSSOM's, as the spec
  transcribes it: `serialize` ensures `serialize_ensures` of the view of its argument, given
  that the argument's ranges and its list are well-formed (`ranges_wf`, `list_wf`), which
  every result of `parse_selector` is (it ensures `exec_check::checked`); identifier and string escaping
  and the pieces down to the simple selector are proven too. The `<an+b>` text is
  `clazel-css`'s proven `write_a_n_plus_b`.
- **Parsing** (`src/exec_parse.rs`) is proven equal to the spec: `parse_selector` ensures
  `parse_selector_ensures` (`src/contract.rs`) of the view of its result, so a result is
  always the spec's `parse_a_selector`, and the parser can give failure where the spec does
  not only if functions nest more deeply than `MAX_NESTING` (32). Each function below it
  (type, attribute, pseudo-element and subclass selectors, the compound and complex
  selector loops, the selector list, the forgiving list of `:is()` and `:where()`, and
  `<an+b>` in `src/exec_anb.rs`) ensures its relation to the spec function of the same name;
  a selector not yet in a list is viewed in the arrays as they are, and appending to the
  arrays leaves every earlier view as it was (`src/exec_grow.rs`). Its result is also
  `exec_check::checked` (`ranges_wf` and `list_wf`, from `theorem_parse_total`), which
  matching and the serializer need. Two things the proof relies on and does not derive:
  `src/exec_numbers.rs` proves, from `clazel-css`'s tokenizer spec, that an integer token's
  number part is its sign and digits with no exponent (so that `<an+b>` can read its value);
  and one axiom (`src/axioms.rs`, counted in the status table): a `Vec` of the parsed arrays
  never holds `usize::MAX` elements, which Verus's model of `Vec` leaves out and Rust's
  allocator guarantees. `<an+b>` keeps each of A and B within 2^32 until the end, so that the
  value of `-b` for a `b` of 2^31 or more clamps as the spec does; the parser clamped `b`
  first and gave -(2^31 - 1) there before this proof.
- Theorems about the spec, in `src/lemmas.rs`: `theorem_parse_total`,
  `theorem_match_total`, `theorem_specificity_monotone`, `theorem_where_zero` and
  `theorem_is_most_specific`. `theorem_parse_total` says that the spec's parse
  (`parse_a_selector`) is a total function (Verus checks that each spec function it calls
  terminates) and that whenever it returns a selector list, the list is not empty and every
  complex selector in it is well-formed (`parse_total`, `src/contract.rs`). It says nothing
  about *which* inputs are accepted: a spec parser that always failed would satisfy it. What
  the spec accepts and builds is checked only by the tests and the mutations below; that the
  parser is the spec is the proof above.
- `mutations.json`: 123 mutations of the spec, each with a certificate in
  `src/examples.rs` (one example per mutation, a theorem about the spec): 45 of the
  original set, one per simple selector, combinator, specificity rule and the quirks rule;
  27 of the grammar (type, attribute, pseudo-element, subclass, compound, complex and list
  productions); 2 of `clamp`; 7 of matching (attribute names, `count_from`, compounds,
  lists); 6 of specificity (saturation, the sums); and 36 of the serialization spec (CSSOM's
  identifier and string escaping, matchers, flags, prefixes, combinators, separators). The
  parser and serializer themselves are not mutated: a mutation of the spec shows that an
  example is false for it, not that the shipped parser agrees; that is what the tests below
  are for.

Tests, which are the evidence that the spec says what the standard does (the parser is proven equal to the spec):

- `tests/parse_structure.rs` decodes what `parse_selector` builds, without the serializer,
  and compares it with trees written from the Selectors 4 grammar, with the inputs the
  grammar rejects.
- `tests/matching_through_parser.rs` parses and matches on a document with SVG and
  no-namespace elements, `:nth-*` with negative and zero `A`, `:empty`, `:not()` with
  complex arguments, and `MAX_NESTING` at 32 and 33; and it holds the ignored test of the
  nested-function cost above.
- `tests/serialize_escaping.rs` checks the serializer's escaping against CSSOM and its
  hand-copied range table of non-ASCII ident code points against CSS Syntax's list and
  `clazel-css`'s tokenizer.
- `tests/specificity_structure.rs` checks §17 for pseudo-elements, `:nth-*`, mixed
  `:is()`, `:not()` and `:where()` lists, and each selector of a list. Saturation cannot
  be reached from a test (it takes 2^32 evaluations), so the mutation `saturate-limit`
  pins it in the spec.
- `tests/conformance_selectors.rs` runs WPT's `css/selectors/parsing` (vendored in
  `tests/data/`, with what it is in its `SOURCE.md`). Each expected failure has a class, a
  reason and the exact way it fails (parsed as invalid, or the serialization it gets), and
  each class has a pinned count. The 60 cases WPT calls invalid on pages of unsupported
  features (`:has()`, `::part()`, `::slotted()`, `:state()`, `:heading`) are rejected only
  because the whole feature is, so they are counted as expected failures, not passes. It
  also checks matching and §17's specificity examples on small arenas.

- `tests/conformance_differential.rs` runs Servo's `selectors` 0.36.1 (the engine of Servo
  and, in its Rust form, Firefox) on the same inputs: parsing, serialization and the
  specificity of each selector of the WPT table (434 inputs: 410 agree, 24 differ for
  listed reasons) and of 6000 generated selectors (half of them with no pseudo-element and
  no mutation, for which nothing is excused: 3000 of 3000 agree), and the matching of every
  generated selector both parse on every element of generated documents (about 1.1 million
  checks, 49,000 of them matches, no difference). Servo is given a `selectors::Element` over
  the `clazel-dom` arena, read through the arena's public readers, and the subset's
  pseudo-classes and pseudo-elements; what that adapter decides is only what the Selectors
  text leaves to the host. Four differences are listed in the test, each with a reason and a
  predicate (Servo keeps the text of a dropped item of a forgiving list when it serializes;
  it accepts a pseudo-class other than a user action one after a pseudo-element; `:host()`;
  a stray `]` inside `:is()`), and the test fails on any other.

An independent transcription (`src/independent.rs`, written from Selectors 4 at the pinned
commit before this crate's spec was opened; its header says what changed after, and why) is
proven equal to the spec in part:

- `theorem_specificity_equivalent` (`src/independent_equivalence.rs`): equal specificity, for
  every selector list both support.
- `theorem_match_equivalent` (`src/independent_match.rs`): the same elements match, in a
  well-formed arena whose elements have no repeated attribute (the spec reads an ID or class
  from the first attribute of that name, the transcription from any).
- `theorem_parse_spec_to_transcription` and `theorem_parse_transcription_to_spec`
  (`src/independent_parse.rs`): the two parse a list of component values alike, and each
  accepts what the other does, including the arguments of `:is()`, `:where()` (forgiving
  list), `:not()` (strict list) and the `:nth-` family (`An+B`).

"Support" differs: the spec has `:link`, `:visited`, `:any-link`, the user action
pseudo-classes and pseudo-elements, which the transcription takes as invalid, so they are
outside every theorem; the transcription has `:has()`, `:scope`, `:defined` and
`:nth-child(An+B of S)`, which are off (`ICtx::ext`) in each theorem. Both are two AI readings
of one text, so they can share a misreading: the weight of evidence for the spec is the WPT
suite above, which the transcription has not been run against.

Tier 2, the target, since this crate parses selectors that a page chose: the parser, the
serializer, matching and specificity are proven equal to the spec, the independent
transcription's equivalence covers parsing in full, every mutation is killed, and the
conformance suites and the differential against Servo's `selectors` are in. The tier was set
from a whole-crate `cargo verus verify` (737 verified, 0 errors) and the crate's tests;
CI's full verification on the pull request is what confirms it.
