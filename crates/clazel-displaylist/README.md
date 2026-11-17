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

Phase 6 item 6.10 added the image items (tags 7 to 9: upload image, draw image, free
image): images are a second table in the retained state, with their own ids below 2^16,
sides of 1 to 2^14 and at most 2^28 live pixel bytes, and a draw must name a live image
with its source rectangle inside it. The list's byte limit grew by 2^28 for the
uploads. `theorem_validated_bounds` covers the image bytes and the source rectangles, and
`independent.rs` and the mutations cover the new items. `clazel-gpu` refuses a list that
holds an image item until item 6.12 gives it textures.

Not yet at its target tier: `Cargo.toml` still says tier 0, since raising it needs
CI's full verification to pass on the pull request (CLAUDE.md rule 7). The limits in
`src/spec.rs` are provisional until items 5.26 and 6.12 measure them, and
`independent.rs`'s extension for the image items was written by the session that wrote the
spec's, not blind (its header says so).
