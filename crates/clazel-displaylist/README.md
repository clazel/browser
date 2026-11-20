# clazel-displaylist

The display list for Clazel's Phase 5 browser: what a renderer asks the GPU process
to draw, its byte format, and the validator every list passes before any GPU call.
Part of [Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

The GPU process holds a graphics driver and must assume a compromised renderer wrote
the bytes it reads, so this crate is the whole of what `clazel-gpu` relies on. A list
holds no shader, pipeline, buffer offset or handle.

The format and the rules are this project's, so `src/spec.rs` is the definition, with
no standard behind it.

Proven with Verus: the encoder, decoder and validator meet their contracts; decoding
and encoding are exact inverses, so bytes have one reading; a list's items never
outnumber its bytes; and a list that passes has every number in range, clips balanced
and within their depth, and every mask it draws live at that point.

Tier 2 (`Cargo.toml`), which stands only once CI's full verification of the pull request
that raised it is green. The evidence it rests on:

- **Mutations**: 79 mutations of the spec in `mutations.json`, every one a `killed` with a
  certificate Verus checks.
- **An independent reading** (`src/independent.rs`), proven equal to the spec: the bytes
  as a run of items (`theorem_read_equals_decode`) and the rules as a fold over them
  (`theorem_check_equals_validate`). The format is this project's own, so there is no
  second standard; the second text is the paragraph "The format, as designed" of item
  5.17a in `docs/phases/phase-5.md`, which was written by the same session as `spec.rs`. It can
  catch a slip in the spec or the paragraph, not a misreading both share. The file's header
  says what was read before its definitions and what the equivalence leaves out (the width
  and height stored with a mask).
- **Conformance** (`tests/conformance_list.rs`): a second decoder and validator written in
  the test, round trips and mutated bytes; no outside suite exists for a format of ours.

The limits in `src/spec.rs` are provisional until item 5.26 measures them.
