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
| `src/proofs.rs` | the Kani harnesses (and two in `src/idct.rs`) |

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

Statements are in `src/proofs.rs` and `src/idct.rs`.

Run in WSL Ubuntu with Kani 0.68.0 (`cargo kani -p clazel-jpeg --harness NAME`), each harness on its own: **12 harnesses, 12 pass**.

| Harness | Statement (every one: no panic, no overflow, no out-of-bounds index) | Bound | Time |
|---------|-----------|-------|------|
| `bit_reader_any` | bits come most significant first; a loaded byte gives exactly 8 | any state with the invariant | seconds |
| `huffman_step_any` | F.16 decoding: any bits end in a symbol or an error within 16 bits; the code grows one bit per step | **any** table with `Table::inv` (not only those construction makes) | 9 s |
| `block_machine_any` | one bit of a block in any stage keeps the block invariant | any block with the invariant, any pair of tables with the invariant, any predictor | 19 s |
| `one_d_pass1_any`, `one_d_pass2_any` | the integer IDCT never overflows `i64`: pass 1 over inputs up to 2^31 (an `i16` times a `u16`) gives descaled outputs up to 2^37; pass 2 over inputs up to 2^37 does not overflow; **composed, `idct` returns `Some` for every block and every quantizer** (the composition is argued here, not a harness) | every input in those ranges | 15 s, 10 s |
| `range_limit_any` | the post-IDCT clamp is the level shift and clamp on -512 to 511, with libjpeg-turbo's wrap-around of period 1024 beyond | every `i64` | 4 s |
| `sample_any` | upsampling returns a sample at every position of the image | every geometry up to 16 by 16, every ratio 1 to 4 each way, any samples and padding | 12 s |
| `sample_constant` | a constant plane stays constant | the same | 40 s |
| `orient_any` | the orientation map stays inside the oriented image and refuses positions outside | every size up to 2^14 by 2^14, every orientation | 4 s |
| `orient_bijection` | each orientation is a bijection onto the oriented image | every size up to 3 by 3 | 167 s |
| `ycc_any` | YCbCr to RGB equals the closed form of libjpeg-turbo's tables | all 2^24 inputs | 12 s |
| `cmyk_any` | CMYK to RGB is `round(c * k / 255)` and never above `c` or `k` | all 2^32 inputs | 5 s |

### What Kani does not cover (not done)

- **Huffman table construction (`Table::build`) has no harness**: the model
  checker's memory grew without bound on it (it also took the shared WSL
  machine down, three times). It is covered by unit tests, by 134 files whose
  tables it built, and `huffman_step_any` takes any table, not only those it
  builds.
- **The marker state machine and the entropy pipeline have no harness**:
  harnesses over the whole state (`control_byte`, `end_segment`,
  `finish_frame`, `finish_scan_header`, the DQT and DHT byte functions, one bit
  through block decoding, IDCT and store) were written and one of them ran
  more than 25 minutes without finishing, so they were removed rather than
  left unrun in the crate. The code is checked arithmetic and `get` only
  (workspace lints), which the model checker would confirm; that is argued,
  not proven. The step function is therefore not machine-checked, and nor is
  the invariant `Jpeg::state_inv` being kept. `block_machine_any` (the block
  decoder) and the leaf functions are.
- **A single harness over all of `idct`** was tried and not finished; the two
  harnesses above stand in for it.
- The Kani numbers are for small bounds where stated; the code is the same
  code at the real sizes (the 12 harnesses above bound only table size,
  sampling geometry and image size for the pure functions).

The tier stays 0 until CI's full verification has run these (CLAUDE.md
rule 7).
