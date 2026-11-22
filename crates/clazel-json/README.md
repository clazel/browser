# clazel-json

JSON text to values, and `JSON.stringify`'s string quoting, specified for
formal verification with Verus. Part of [Clazel](../../README.md), a web
browser built from the bottom up by AI using formal verification instead of
trust.

## What it is

- the ECMA-404 grammar, and the value ECMA-262's `JSON.parse` constructs from
  a text that matches it (reviving is out of scope), as a tree this crate
  owns, not the JavaScript heap's objects;
- QuoteJSONString (ECMA-262 §25.5.2.3†).

Strings are `u32` code points on the way in and `u16` code units in values,
as a JavaScript string is. Numbers keep their source text: their Number value
belongs to `clazel-js-number`. Arrays and objects may nest `max_depth()`
(512) levels; a deeper text is an error, a listed deviation from the
standard, which sets no bound.

## Status

**Tier 0 today; target tier 2.** The spec, the contracts, the examples and
the certified mutations were committed first; then the executable parser
(`parse::parse`) and quoter (`quote::quote`), each proven by Verus to equal
the spec on every input (no precondition), and so free of panics and
overflow. Still to do before the tier is raised: the independent
transcription from RFC 8259 proven equal to the spec, conformance tests
against official suites (JSONTestSuite, Test262's `built-ins/JSON`), and a
full `cargo xtask verify` in CI. `tests/behaviour.rs` is a hand-written
check of the spec's reading, not a conformance suite.

Nothing here is verified against the standard's text yet: the spec was
written without access to ECMA-404 or ECMA-262, and its header says so (the
† mark is the convention in `docs/phases/phase-7.md`).

## Layout

`src/spec.rs` (the transcription), `src/tree.rs` (the executable tree and
its meaning), `src/contract.rs`, `src/parse.rs` and `src/quote.rs` (the
executable code and its proofs), `src/examples.rs`, `src/lemmas.rs` and
`mutations.json`, as in `clazel-base64`.
