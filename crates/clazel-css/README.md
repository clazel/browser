# clazel-css

CSS parsing for Clazel's Phase 5 browser. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

The decoding of input bytes (§3.2), the tokenizer and the parser are here, each proven
equal to its spec, with certified mutations: `src/parser/exec_parse.rs` has the parser's
entry points, and item 5.3 of the plan says how it reads tokens and what it costs. Of the
five theorems stated in `src/parser/contract.rs` that `src/parser/lemmas.rs` leaves out,
`src/parser/theorems.rs` proves two (`output_preserved`, and `value_end` for the starts
inside a stream, the only ones where its `subrange` means anything); `block_ends_agree`,
`spans_in_order` and `parse_bounded` are not proven. The crate also holds the test
data of [item 5.1](../../docs/phases/phase-5.md), in `tests/data/`: `css-parsing-tests`
and WPT's `css/css-syntax`, each with what it is and where it falls short in its
`SOURCE.md`. `tests/conformance_tokens.rs` and `tests/conformance_input.rs` run the cases
that need no parser, `tests/conformance_syntax.rs` runs the parser's and lists each
expected failure with its reason, and `tests/bombs.rs` runs sheets written to hurt the
parser.

`src/independent.rs` is a second transcription of the tokenizer (with "filter code
points") and the parser, written from the pinned text of CSS Syntax 3 without reading
the spec, and proven equal to it: the tokenizer, every algorithm of §5.4 and every entry
point of §5.3 that takes a string, over every stream of code points. Its header says what
was read before the definitions were committed, and what it does not cover (the input byte
stream, the An+B microsyntax, its serialization, the "parse according to a grammar" hooks
and three entry points on lists of tokens and of component values, in a second round, also
proven equal; the entry points that read a source text on such lists, and the composition
of decoding with an entry point, are not covered, and the text is the same one the spec
transcribes, not CSS 2.1 as item 5.4 had proposed).

Tier 2, the target for a crate that parses style sheets a page chose: the conformance
suites above, the certified mutations and the independent transcription are all there.
What it does not claim is in the notes above and in the header of `src/independent.rs`;
the theorems of `src/parser/contract.rs` that are stated and not proven (`block_ends_agree`,
`spans_in_order`, `parse_bounded`) are not part of the tier.
