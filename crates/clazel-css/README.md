# clazel-css

CSS parsing for Clazel's Phase 5 browser. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

The tokenizer and the parser are here, each proven equal to its spec, with certified
mutations: `src/parser/exec_parse.rs` has the parser's entry points, and item 5.3 of the
plan says how it reads tokens and what it costs. Five theorems stated in
`src/parser/contract.rs` are not proven. The decoding of input bytes (§3.2) is not here
yet. The crate also holds the test data of
[item 5.1](../../docs/phases/phase-5.md), in `tests/data/`: `css-parsing-tests` and
WPT's `css/css-syntax`, each with what it is and where it falls short in its
`SOURCE.md`. `tests/conformance_tokens.rs` runs the cases the tokenizer alone can
answer, `tests/conformance_syntax.rs` runs the parser's and lists each expected failure
with its reason, and `tests/bombs.rs` runs sheets written to hurt the parser.

Tier 0 for now: a tier also needs an independent transcription and full conformance,
which are still to come. The target is tier 2, since this crate will parse style
sheets that a page chose.
