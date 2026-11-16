# clazel-deflate

DEFLATE (RFC 1951) and zlib (RFC 1950) decoding for [Clazel](../../README.md),
a web browser whose parsers of untrusted input carry machine-checked proofs.
Phase 6 item 6.2 (`docs/phases/phase-6.md`). PNG (item 6.4) feeds its `IDAT`
chunks through it, in the renderer's sandbox, on bytes a page chose. Target
tier 2 (decision 6.0(a)); **the crate is at tier 0**: see "What is proven".
gzip (RFC 1952, decision 6.0(h)) is not here yet.

## What it does

| File | Holds |
|------|-------|
| `src/spec.rs` | RFC 1951 and RFC 1950 as pure Verus functions of the whole input, with the step and section numbers and every modelling choice listed at the top |
| `src/contract.rs` | what each executable function is meant to satisfy, written before the code |
| `src/lemmas.rs`, `src/examples.rs` | facts proven about the spec; the RFCs' own examples evaluated |
| `src/stream.rs` | `Inflater`, the resumable decoder: `step(src, dst, window)` reads and writes as much as it can and says whether it needs input or output room |
| `src/huffman.rs` | the canonical code of RFC 1951 §3.2.2 as a 15-bit lookup table |
| `src/adler.rs` | Adler-32, in Verus |
| `src/oneshot.rs` | whole-input decoding, for tests and callers that hold the whole stream |

`Inflater` allocates only its three code tables, in `new()`; decoding itself
allocates nothing. The 32 KiB window is a buffer the caller provides, as the
output room is. Every element of the format (a block header, a Huffman code,
a run of extra bits, a stored block's length) is read whole or not at all and
all other progress is in the state, so the input and the output can be cut
anywhere. The output limit is a parameter: a stream that would make more
output than `limit` fails with `Error::OutputLimit` after producing no more
than `limit` bytes, so a decompression bomb stops.

Where the RFCs are silent the spec decides, and lists it: incomplete and
over-subscribed codes are refused as zlib refuses them, FDICT is refused,
HLIT above 286 is refused, distance codes 30 and 31 and length symbols 286
and 287 are refused when used. `docs/ERRATA.md` records one place where the
RFC contradicts itself (the bit order of the extra bits).

## What is proven (and what is not)

Verus `0.2026.10.04.426d8b0`, run in WSL: **37 verified, 0 errors** (`cargo verus verify -p clazel-deflate`, the whole crate).

- **The spec is well-formed:** every spec function terminates (Verus checks
  each `decreases`).
- **About the spec** (`src/lemmas.rs`, `src/lemmas_usable.rs`, `src/examples.rs`): the
  length and distance tables are chains of consecutive ranges, ending at 258
  and 32,768 (the RFC's tables, restated as a property); the RFC's own worked
  examples of §3.2.2 (ABCD and ABCDEFGH) give the codes it lists;
  `code_usable` accepts and refuses the small sets of lengths it should
  (complete, one code of length 1, none, incomplete, over-subscribed, too
  long); every way a zlib header can be wrong gives its error.
- **`theorem_output_bounded`**: for every input and limit, a successful
  `inflate` or `zlib_decompress` produced at most `limit` bytes (about the
  spec, by induction over the blocks and symbols).
- **`adler::update` and `adler::adler32`** are proven equal to the spec's
  Adler-32 (no overflow, no panic), for every input.
- **Mutations** (`mutations.json`): 88 mutations of the spec, **88 killed**, each with a certificate
  that Verus checks (`cargo xtask mutate clazel-deflate`): every length base
  (29), every distance base (30), the extra-bit count of every group of codes
  (6 length, 14 distance), the rules of `code_usable` (incomplete, empty,
  over-subscribed, too long, the code length code), and the zlib header checks
  (FCHECK, method, window, dictionary). Verus: 37 verified (the whole crate,
  with `certs.rs`).

**Not proven, and so why the crate is tier 0:**

- `Inflater::step`, `Table::build` and `Table::lookup` are plain Rust: tested
  (below), not proven. So `theorem_chunking_irrelevant`,
  `theorem_inflate_total` and `theorem_huffman_table` (the fast table equals
  the canonical code) of the plan are **statements** in `contract.rs`
  (`chunked_ensures`, `build_table_ensures`), not theorems. The next step is
  the table: `build_table_ensures` over the build loops, then the step
  function against `spec::inflate`.
- No independent transcription (`independent.rs`) of RFC 1951's prose, and no
  mutation of the decoding steps (the block loop, the dynamic header): the
  mutations cover the tables, the usable-code rule, and the checks that a
  short stream can witness. Tier 2 needs both.
- No Kani harnesses, no Miri run measured for the new tests beyond the strides
  in the test file.
- `fixed` blocks assume the fixed codes are complete (they are: Kraft's sum is
  1); the decoder's `build` result for them is ignored and a test checks it.
- Not a fast decoder: one table lookup per symbol and a byte at a time through
  the bit buffer. Speed is not a goal of this item.

## Tests (`tests/conformance_deflate.rs`)

12 tests, each of which passes.

- Wuffs' `test/data` streams and `artificial-deflate` corner cases (commit
  `b36a81d`, MIT or Apache-2.0 at our choice): the five full streams decode to
  exactly the text beside them and use every byte, the six corner cases to
  their `.decompressed` file, `distance-code-31` fails as it must.
- A differential against `miniz_oxide` 0.9.1 over 33,979 streams (the
  vendored ones, `miniz_oxide`'s compressor at levels 0, 1, 6 and 9 over five
  kinds of data, hand-made ones, each with truncations, bit flips and random
  changes): the two decoders accept the same streams with the same output (the number of streams is in the test output; no difference was
  seen, so the test lists none).
- The decoder equals a naive Rust transcription of the spec (`tests/model`,
  written without looking at `src/stream.rs`) on 12,119 streams, errors
  included.
- Every chunk size of the input (1 to the whole) and every size of the output
  room give the whole-input result, on every stream and on mutants.
- A hand-made stream for each `Error`; every length and distance code; stored
  blocks, empty and 65,535 bytes long, after a block that does not end on a
  byte boundary; a dynamic block with a hand-made code; bytes after the stream
  are not read.
- The limit: exact (a limit of the output's length succeeds, one less stops),
  and a 64 MiB stream of zeros stops at a 1 MiB limit.

## Trust

The proofs assume the Rust compiler and Verus, and that the spec matches the
RFCs, which the examples, the model test and the differential support but
cannot prove. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).
