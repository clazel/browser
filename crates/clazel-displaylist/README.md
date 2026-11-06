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

Not yet at its target tier: `independent.rs` and certified mutations are still to come,
and the limits in `src/spec.rs` are provisional until item 5.26 measures them.
