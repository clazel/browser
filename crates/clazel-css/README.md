# clazel-css

CSS parsing for Clazel's Phase 5 browser. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

The tokenizer is here, proven equal to its spec. The parser has its spec, contracts and
some theorems (`src/parser/`), and no code yet: item 5.3 of the plan says how it will read
tokens and what it will cost. The crate also holds the test data of
[item 5.1](../../docs/phases/phase-5.md) that the tokenizer of item 5.2 will be
tested against: `css-parsing-tests`, in `tests/data/`, with what it is and where it
falls short in its `SOURCE.md`.

Tier 0 for now: a tier also needs mutations, an independent transcription and full
conformance, which are still to come. The target is tier
2, since this crate will parse style sheets that a page chose.
