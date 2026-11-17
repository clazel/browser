# clazel-jpeg

A baseline JPEG decoder for [Clazel](../../README.md), a web browser whose
parsers of untrusted input carry machine-checked proofs. Phase 6 item 6.5
(`docs/phases/phase-6.md`). It implements the one interface of every Phase 6
decoder, `clazel_image_shape::Decoder` (item 6.3): a resumable step function
over caller-owned buffers, nothing allocated while decoding. Its only
dependency is `clazel-image-shape`.

## What it does

ITU-T T.81 sequential DCT with Huffman coding: SOF0 and SOF1 (8-bit), DHT,
DQT (8 and 16-bit), DRI and restart markers, SOS with interleaved scans or one
scan per component, APPn and COM skipped, EOI; 1, 3 or 4 components at
sampling factors 1 to 4 that divide the largest. Progressive (SOF2) is item 6.6
and is refused with `Error::Unsupported`, as are arithmetic, lossless,
hierarchical, 12-bit and two-component files. Output is opaque straight RGBA8.
Listed choices, each with its reason, are in `src/lib.rs`: libjpeg-turbo's
`jidctint` IDCT and "fancy" upsampling, JFIF colour, Adobe APP14 (inverted
CMYK and YCCK), EXIF Orientation only.

| File | Holds |
|------|-------|
| `src/lib.rs` | the standards, the clause numbers, the listed choices |
| `src/decoder.rs` | the marker state machine, scans, `Jpeg`, `Decoder`, the invariant |
| `src/block.rs` | one block, bit by bit (T.81 F.2.2, Figures F.12, F.13) |
| `src/huffman.rs` | Annex C construction, Figures F.15 and F.16 decoding |
| `src/bits.rs` | the bit reader |
| `src/idct.rs` | dequantization and the integer IDCT |
| `src/output.rs` | upsampling, YCbCr, CMYK, orientation (pure functions of one position) |
| `src/exif.rs`, `src/markers.rs`, `src/header.rs` | Orientation, marker classes, `decode_config` |
| `src/proofs.rs`, `src/decoder_proofs.rs` | the Kani harnesses |

The work buffer is the worst case for the config, four planes of
`(w + 31) * (h + 31)` bytes, because `work_len` is a function of the config
alone and the sampling factors are in the frame header. A caller bounding
memory counts it. Not benchmarked or optimised: entropy decoding is one bit
per call.

## Tests (`tests/conformance_jpeg.rs`)

Against **libjpeg-turbo's output**: libjpeg-turbo 3.2.1's `testorig.jpg` and
`testimgint.jpg` (its `testimages/`), and a corpus of 132 files made by
`scripts/jpeg-reference.py` (every sampling ratio, restart intervals,
interleaved and non-interleaved scans, gray, YCbCr, RGB, CMYK, YCCK, SOF1,
16-bit tables, sizes 1 by 1 to 227 by 149, the eight EXIF orientations).
**134 files, 2,065,288 samples, every one exactly equal (tolerance 0, the
expected value)**: the difference histogram is printed with the suite line.
`testimgari.jpg` (arithmetic) and `monkey12.jpg` (12-bit) are refused. Every
file at chunk sizes 1 to 4096 equals the whole-file decode; 2,680 byte mutants
never panic; hand-made streams cover DC prediction, restart intervals and the
marker errors. Changing one constant of the IDCT or the upsampling by one makes
the differential fail (tried).

**The reference is libjpeg-turbo 2.1.5, not 3.2.1.** The references come from
the installed Ubuntu 24.04 `libjpeg-turbo8` 2.1.5 through `ctypes` (defaults:
ISLOW IDCT, fancy upsampling). Building the pinned 3.2.1 sources was refused
by the session's permission system, so it was not done; regenerate with
`scripts/jpeg-reference.py` against 3.2.1 when it can be. ITU-T T.83's
conformance streams are the gap 6.1 recorded: not used. `zune-jpeg` was not
added (no row in `docs/DEPENDENCIES.md`): the reference is libjpeg-turbo. CMYK
is compared after the same `C * K / 255` conversion (libjpeg gives CMYK), so
that conversion is checked against itself only.

## Kani harnesses

See `src/proofs.rs` and `src/decoder_proofs.rs` for the statements; results
and bounds are in the table below.

RESULTS_TABLE

The tier stays 0 until CI's full verification has run these (CLAUDE.md
rule 7).
