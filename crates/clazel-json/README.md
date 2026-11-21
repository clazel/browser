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

**Tier 0 today; target tier 2.** This change adds the spec, the contracts
and the examples, with the mutations certified. The executable parser and
quoter and their proofs come next, then the independent transcription from
RFC 8259 and the conformance tests. Nothing here is verified against the
standard's text yet: the spec was written without access to ECMA-404 or
ECMA-262, and its header says so (the † mark is the convention in
`docs/phases/phase-7.md`).

## Layout

`src/spec.rs` (the transcription), `src/tree.rs` (the executable tree and
its meaning), `src/contract.rs`, `src/examples.rs`, `src/lemmas.rs` and
`mutations.json`, as in `clazel-base64`.
