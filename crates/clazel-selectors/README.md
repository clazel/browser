# clazel-selectors

CSS selectors for Clazel's Phase 5 browser. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

There is no code here yet. The crate holds the test data of
[item 5.1](../../docs/phases/phase-5.md) that the selector parser of item 5.5 will be
tested against: WPT's `css/selectors/parsing`, in `tests/data/`, with what it is and
where it falls short in its `SOURCE.md`.

Tier 0 for now. The target is tier 2, since this crate will parse selectors that a
page chose.
