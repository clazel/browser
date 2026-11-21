# clazel-webp

A WebP decoder for [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs. Phase 6 item 6.8
(`docs/phases/phase-6.md`): the RIFF container, animation, and **lossless**
(VP8L) decoding; and item 6.9, **lossy** VP8 key frames (RFC 6386) with the
`ALPH` alpha plane (see "Lossy" below). It runs in the renderer's sandbox, on bytes
a page chose, and implements the one interface of every Phase 6 decoder,
`clazel_image_shape::Decoder` (item 6.3): a resumable step function over
caller-owned buffers, nothing allocated while decoding.

Its only dependency is `clazel-image-shape`. `image-webp` is a dev-dependency,
used only by the differential test.

## What it does

RFC 9649 (the WebP container, and the lossless bitstream): `RIFF`/`WEBP`, the
simple lossless format, the extended format (`VP8X`; `ICCP`, `EXIF`,
`XMP ` and unknown chunks skipped), `ANIM` and `ANMF`. **Every frame** of an
animation is decoded and composited onto the canvas with the previous
frame's disposal and the frame's blending method; after each
`Status::FrameDone` the pixel buffer holds the canvas as displayed with that
frame and `Webp::frame()` has the frame's rectangle, duration, blending and
disposal. VP8L: the four transforms (predictor with its fourteen modes,
colour, subtract green, colour indexing with pixel bundling), the colour
cache (1 to 11 bits), meta prefix codes, simple and normal code length codes,
LZ77 backward references with the distance map.

| File | Holds |
|------|-------|
| `src/lib.rs` | the pinned standard, the section numbers, the listed choices |
| `src/decoder.rs` | the container state machine, `Webp`, `Decoder`, `Webp::state_inv`, compositing |
| `src/vp8l.rs` | the lossless bitstream as a state machine over atomic actions |
| `src/huffman.rs` | canonical prefix codes: construction, decoding without tables |
| `src/transform.rs` | the inverse transforms, one row at a time, in place |
| `src/distance.rs` | the LZ77 prefix coding and the distance map (Figure 20) |
| `src/compose.rs` | alpha blending |
| `src/bits.rs`, `src/work.rs` | the bit reader, the work buffer's layout |
| `src/proofs.rs` | the Kani harnesses |

The work buffer is `work_len(config)`: about 11.6 kB (colour cache, code
lengths, colour table), 12 bytes per block of 4 by 4 pixels (the predictor,
colour transform and entropy images), 6.4 kB per prefix code group held (at
most 1,024, and at most one per block of 4 by 4), and for an animation a
frame buffer as large as the canvas. A still image is decoded straight into
the pixel buffer.

## Listed choices (`src/lib.rs` has them with the section numbers)

Animation canvas transparent black and the `ANIM` background ignored,
disposal to transparent; alpha blending on stored values with libwebp's
integer arithmetic (a destination of alpha 0 takes the source exactly);
`alpha_is_used` ignored; `ANMF`/`ANIM` skipped in a still image, image data
outside a frame in an animation an error; `ALPH` decoded for `VP8 ` images (item 6.9; ignored for `VP8L`); the RIFF size ends
the stream; prefix codes empty, over-subscribed or incomplete are errors and a
single symbol takes zero bits; predictor modes 14 and 15 predict like mode 0;
at most 1,024 prefix code groups (more is `Unsupported`); a backward
reference before the first pixel or past the last is an error.

## Kani harnesses (`src/proofs.rs`)

Sixty-nine from item 6.8 (the count of 6.9 is below). The step harnesses are one per phase, role or transform: with
the phase symbolic, CBMC ran out of memory (over 4 GB locally; on CI the
runner was lost after two hours). What keeps each in memory is listed at the
top of `src/proofs.rs` (MiniSat for the pixel, finish and container ones,
smaller unwinding, a 4-colour table where it is indexed symbolically).
**Not yet run green on CI**: locally, under Kani 0.68.0 with a 4 GB cap, each
was run on its own (results in the pull request); CI's approved proof jobs
are the result that counts.

| Harness | Statement (every one: no panic, no overflow, no out-of-bounds index) | Bound |
|---------|-----------|-------|
| `huffman_build_any` | prefix code construction: an error if a length is over 15; otherwise complete (Kraft sum exactly 1) or a single symbol, each used symbol once in the table | **any code lengths**, 6 symbols |
| `huffman_decode_any` | decoding: a symbol of the alphabet with the code's length, never more bits than available, `More` only under 15 bits | any built code, any 32 bits, any count available |
| `distance_value_any` | the LZ77 prefix coding: 1 to 1,048,576 | every prefix code 0 to 39, any extra bits |
| `distance_map_any` | the distance of a code is at least 1, `code - 120` above 120, within 7 rows and 8 columns below | every code, every width up to 2^14 |
| `predict_any` | each predictor mode's value (L, T, TR, TL, black, Average2 of L and T, Select is L or T) | every mode, any four pixels |
| `predictor_row_any` | the inverse predictor of a row: the other row untouched, the top-left pixel is black plus residual | any row of 3 pixels in 2 rows, any block bits 2 to 9, any modes, any pixels |
| `color_row_any` | the inverse colour transform: green and alpha unchanged | any row of 3, any transform data |
| `green_row_any` | the inverse subtract green: exactly red and blue gain green | any row of 3 |
| `palette_row_any` | colour indexing with bundling: each pixel is the table entry its packed bits name, or transparent black past the table | every bundling width, rows of 1 to 8 pixels, up to 4 colours |
| `palette_in_place_any` | the same, two rows expanded in place, last row first, equal to the expansion from a copy | every bundling width, 4 pixels in 2 rows |
| `blend_px_any` | alpha blending: alpha 255 gives the source, 0 the destination, otherwise alpha does not go down | any two pixels |
| `act_*` (40, `act_harness!`) | one atomic action of the lossless decoder, in one phase each (header, transforms, cache, meta prefix, every step of reading a prefix code, and pixels: literal symbols, lengths, distances, cache lookups, a backward reference of at most 4 pixels), keeps `Vp8l::inv` on `Ok`; the two distance phases have one harness per role | any state with the invariant, any bits, any contents of every scratch region; images of at most 4 pixels; `act_build_code`: an alphabet of at most 8 symbols; palette role: a table of 4 colours |
| `finish_*` (9) | finishing an image keeps `Vp8l::inv`: the colour table, entropy image and two transform images, and the main image with no transform or with one of each kind (inverting several is a loop whose body depends only on that transform and the pixels) | the same, up to 4 colours, 2 rows; `finish_main_predictor` exactly 2 by 2 pixels (`predictor_row_any` covers rows of 3); `finish_main_index`: a table of 4 colours |
| `container_*` (9, `container_harness!`) | one byte of the container, in each phase but the lossless payload, keeps `Webp::state_inv` on `Ok` | any state with the invariant, a 2 by 2 canvas |

### What Kani covers, and what it does not

- **The step function itself is not machine-checked, its parts are.** Item
  6.3's template `decoder_step_harness!` was not instantiated: GIF's
  experience (item 6.7) is that CBMC does not finish on a whole state machine
  of this size, and this one is larger (a work buffer of 15 kB even at the
  harness's sizes). `step` is `Parts::new` (a unit test and the lengths in
  `inv`), then a loop of `Webp::byte`, which is `dispatch` (the container
  harness) and, in a lossless payload, `Vp8l::push` and `Vp8l::advance`, a
  loop of `Vp8l::act` (one harness per phase) and `finish_image` (one per
  role). What the template would add and is argued here, not
  proven: that `inv` is kept over several bytes (induction from one), that
  `consumed <= chunk.len()` and that `NeedMore` consumes the chunk (a loop's
  index), and that nothing outside the buffers is written (safe Rust
  bounds-checks every index, and no index uses unchecked arithmetic: the
  workspace lints deny it).
- **Small bounds.** Under Kani the colour cache is 8 entries (`work.rs`), so a
  green alphabet is 288 symbols; images are at most 4 pixels; a backward
  reference at most 4 pixels. The code is the same code with other
  constants; the real sizes are run by the unit tests, the differential test
  and Miri.
- **Separate arrays**: the harnesses give the scratch regions as separate
  arrays, not one work buffer cut by `Parts::new`.
- **Not stated**: that the pixels are right (the differential test's and the
  hand-made streams'), that the work is bounded in time (an image of 2^26
  pixels coded with zero-bit prefix codes decodes from a handful of bytes:
  the limits of item 6.0(j) bound it), and that every state `inv` admits is
  reachable (it over-approximates, so the harnesses are sound).
- The tier stays 0 until CI's full verification has run these green
  (CLAUDE.md rule 7).

## Tests

- **Unit tests** (22): the bit reader, the layout, prefix codes (the RFC
  example, one symbol, bad codes), the distance map and Table 4, each
  transform and predictor border, blending.
- **`tests/conformance_webp.rs`** (15 tests): Wuffs' WebP test data
  (`tests/data/wuffs-webp`, commit `b36a81d`, MIT or Apache-2.0 at our
  choice; libwebp's own vectors have no licence and are not vendored)
  against `image-webp` 0.2.4: **the 11 lossless files agree, exactly**
  (the largest 1,165 by 859); the animation agrees on its first frame and
  within 1 per channel on the alpha-blended ones (`image-webp` rounds blending
  more precisely than libwebp's formula, which is followed: listed); the 2
  lossy files are 6.9's, see "Lossy". Every file at
  chunk sizes 1 to 4096 (with and without empty chunks) equals the
  whole-file decode, with the invariant checked at every step and canary
  bytes past the buffers untouched. 1,440 deterministic byte mutants
  never panic (968 end in an error, the rest decode something).
- **`tests/handmade/`**: a VP8L encoder written for the tests (from the RFC,
  sharing no code with the decoder) makes **531 images** that must decode to
  exactly the source, byte by byte, whole, and as `image-webp` reads them:
  ten orders of transforms at six sizes and six seeds (360), every predictor
  mode (6), pixel bundling at every palette size from 1 to 256 and nine
  widths (81), caches of 0 to 11 bits with and without meta prefix codes (72),
  backward references of every distance code and simple and normal prefix
  codes (12). Container cases: a still `VP8X` with chunks to skip and
  trailing data; an animation of five frames with blending, no blending and
  both disposals, checked against a compositor written in the test; eight
  malformed files and four malformed streams, each refused with the right
  reason.
- **Miri**: every test runs a stride (`cfg!(miri)`): the 156-byte file, chunk
  size 1, 2 mutants, one hand-made image of at most 8 by 4 pixels. Miri runs
  25,000 to 30,000 times slower than native; measured with `--cfg miri`
  natively, the 156-byte file decodes in 0.85 ms.

## Lossy (item 6.9)

`src/vp8/` follows RFC 6386 (pinned in `vp8/mod.rs`, which also lists its
choices): `bool_decoder.rs` (§7), `header.rs` (§9, 19), `quant.rs` (§9.6,
14.1), `tables.rs` (extracted from the RFC's text by script), `tokens.rs`
(§13), `transform.rs` (§14.3, 14.4, 14.5), `predict.rs` and `plane.rs` (§12),
`loop_filter.rs` (§15), `yuv.rs` (libwebp's conversion, a listed choice);
`src/alpha.rs` is `ALPH` (RFC 9649 §2.7.1.2). The whole `VP8 ` chunk is kept
(in the frame's RGBA buffer, or 1 kB of work space if small) and the frame is
decoded, filtered and converted in the `step` that gives its last byte. **The
work buffer grew** by about 2.6 bytes per pixel for every WebP, lossless too
(alpha plane and lossy planes: the config cannot say which codec a file uses).

State, honestly: **built; tier unchanged at 0; Kani not run locally.** Eight new
harnesses are written in `src/proofs.rs` (boolean decoder, every subblock mode,
whole-block modes at the frame edges, the three loop filters, both transforms,
YUV to RGB, container bytes in the `ALPH` and `VP8 ` phases) and have not been
compiled under Kani or run; CI's proof jobs need approval. The whole-frame
decode is not harnessed. Tests: all 14 Wuffs lossy files equal `image-webp`
exactly (`tests/data/wuffs-webp`, 12 added); `tests/lossy/` has a VP8 writer
(399 of 400 random frames equal, one refused as over 4 bytes to the pixel) and
48 `ALPH` files (every filter, raw and compressed) equal. libwebp's vectors
and `dwebp` output are not used (no licence): the reference is `image-webp`.

## Not done

The loop count and frame timing policy
(6.19). Prefix code group counts above 1,024 (or above the image's blocks).
libwebp's own test vectors (no licence) and `dwebp`'s output: `image-webp`
is the reference, and libwebp's blending is reproduced from its source's
formula, not compared with it. Kani has not been run on this crate.
