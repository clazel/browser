# clazel-png

A PNG and APNG decoder for [Clazel](../../README.md), a web browser whose
parsers of untrusted input carry machine-checked proofs. Phase 6 item 6.4
(`docs/phases/phase-6.md`). It runs in the renderer's sandbox, on bytes a
page chose, and implements the one interface of every Phase 6 decoder,
`clazel_image_shape::Decoder` (item 6.3): a resumable step function over
caller-owned buffers, nothing allocated while decoding.

Its dependencies are `clazel-image-shape` and `clazel-deflate` (item 6.2:
the streaming zlib it runs the image data through; PNG needs only its
interface, `Inflater::step`, which `src/engine.rs` states as a trait). The
`png` crate is a dev-dependency, used only by the differential tests.

## What it does

PNG Specification, Third Edition (W3C Recommendation, 24 June 2025): the
signature, chunk layout and CRC-32; IHDR (every colour type and bit depth of
Table 11.1, others refused), PLTE, `tRNS`, IDAT across any number of chunks
(empty ones too), IEND; the five filters with their exact modulo-256
arithmetic; Adam7; 1, 2 and 4-bit samples expanded and 16-bit samples
reduced to 8 as the `png` crate does (so the differential is exact);
`gAMA`, `cHRM`, `iCCP`, `sRGB` and `cICP` read and ignored; and APNG:
`acTL`, `fcTL`, `fdAT`, with **every frame** decoded and composited onto the
canvas with its dispose and blend operations. After each `Status::FrameDone`
the pixel buffer holds the canvas as displayed with that frame, and
`Png::frame()` has the frame's rectangle, delay, disposal and blend. The
first `FrameDone` is the image itself (the default image of an APNG), which
decision 6.0(d)'s option A shows.

| File | Holds |
|------|-------|
| `src/lib.rs` | the pinned standard, the section numbers, the listed choices |
| `src/decoder.rs` | the state machine over the chunks, `Png`, `Decoder`, `Png::inv`, the Kani state builders |
| `src/decoder/image.rs` | the image data: frame start and disposal, the zlib loop, one scanline to pixels |
| `src/engine.rs` | the zlib engine as a trait (`Inflater` implements it) |
| `src/crc.rs`, `adam7.rs`, `filter.rs`, `pixel.rs` | CRC-32, the seven passes, the five filters, samples to RGBA and APNG's OVER |
| `src/work.rs` | the layout of the work buffer |
| `src/proofs.rs` | the Kani harnesses |

The work buffer is `work_len(config)`: the zlib window (32 KiB), two
scanlines of up to `8 * width` bytes, the palette as RGBA (1 KiB) and **a
copy of the canvas** (for `dispose_op` "previous"), so a decode needs the
pixel buffer twice over plus about 35 kB and two rows. That copy is a listed
choice (`src/lib.rs` 1): `decode_config` cannot know whether the file is an
APNG, so a still PNG pays for it too; a caller bounding memory counts it,
and 6.12 may size it lazily. `Png<Inflater>` is about 200 KiB (the zlib
engine's code tables), so keep it in a `Box`.

## Listed choices (`src/lib.rs` has them with the section numbers)

The `png` crate's pixel choices: 16 bits truncated to the high byte, 1, 2
and 4 bits scaled by `255 / (2^depth - 1)`, `tRNS` colours compared at full
precision, a palette index past the palette opaque black. No colour
management: gamma, chromaticities, ICC profiles, sRGB and cICP are ignored.
Every chunk's CRC is checked, ancillary ones too (stricter than `png`). The
zlib stream must be exactly the scanlines. FrameDone comes after the CRC of
the chunk that completed the frame. APNG: the canvas starts transparent,
"previous" of the first frame is "background", a default image outside the
animation clears the canvas before the first frame, a missing `acTL` makes
`fcTL` and `fdAT` ignorable, fewer frames than `num_frames` is accepted and
more is an error. `APNG_BLEND_OP_OVER` rounds as `pixel::over` documents.

## Kani harnesses (`src/proofs.rs`)

39 harnesses, all passing: `cargo kani -p clazel-png` ends in `39 successfully verified harnesses, 0 failures` (Kani 0.68.0, CBMC 6.11.0, macOS arm64). The time and memory columns are each harness run **alone** as `/usr/bin/time -l cargo kani -p clazel-png --harness X` (Kani's own "Verification Time"; the peak resident set of the whole command, which is CBMC's), on a machine shared with other builds, so the times are upper bounds. Run one after another they took about 42 minutes in all; the slowest is `unfilter_any` (379.6 s) and the largest memory 3.34 GB. Every one is also a no-panic, no-overflow, no-out-of-bounds proof for the code it runs.

**Pieces** (the filters, Adam7, samples and the CRC, each over its own range):

| Harness | Statement | Bound | Time | Peak memory |
|---------|-----------|-------|------|-------------|
| `paeth_is_the_spec` | the Paeth predictor equals 9.4's formula in `i32` | every `a`, `b`, `c` | 4.3 s | 0.14 GB |
| `unfilter_any` | all five filters equal 9.2's formulas byte by byte, a type above 4 is refused | any row up to **16 bytes** (a 2 by 2 canvas's widest), `bpp` 1 to 8 (`filter_bpp()` is `.max(1)` and is the only caller, `src/decoder/image.rs`; 9.2 rounds bpp up to 1), any `filter` byte | 379.6 s | 0.43 GB |
| `adam7_pixel_in_one_pass` | every pixel is in exactly one pass, at the coordinates the pass gives back, inside the pass's size | **every** width and height 1 to 2^14 | 1.9 s | 0.14 GB |
| `adam7_pass_pixels_in_image` | every pass pixel is inside the image | the same | 0.56 s | 0.14 GB |
| `adam7_whole_image` | a non-interlaced image is one pass, the whole image; pass 1 of it and pass 7 of an interlaced one do not exist | the same | 0.09 s | 0.14 GB |
| `adam7_axis_split` | the pixel counts along one axis split as the passes split the pixels: 0 and 1 modulo 2 add up to the length, 0 and 2 modulo 4 to 0 modulo 2, 0 and 4 modulo 8 to 0 modulo 4 | every length to 2^31 | 0.36 s | 0.14 GB |
| `sample_and_rgba_any` | `sample`, `rgba`, `over` (and `over`'s two identities) | every colour type, depth, index, `tRNS`, palette up to 8 bytes, row up to 8 bytes | 8.0 s | 0.36 GB |
| `crc_update_any` | the CRC update | any register, up to 2 bytes | 2.9 s | 0.15 GB |

**The step function in parts.** The whole `step` is not a harness (below), so the state machine is proven function by function, one harness per phase of `advance` (and for the phases whose work depends on the chunk, per kind of chunk) and per part of the image-data loop. Each runs over any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes, unless its row says more. A symbolic phase keeps every phase's code in the formula (the first attempt, `advance_signature` with the phase symbolic, had not finished after 6 minutes of CBMC and 3.8 GB, for a phase of eight bytes; with the phase a constant it takes 11 seconds), so each harness builds its state field by field with the phase (and the stage or kind) a constant, `with_png_at` in `src/decoder.rs`.

| Harness | Statement | Bound | Time | Peak memory |
|---------|-----------|-------|------|-------------|
| `advance_signature` | `advance` in the phase of: the 8 signature bytes: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 8.3 s | 0.39 GB |
| `advance_header` | `advance` in the phase of: a chunk header: `chunk_start`, every chunk kind and every refusal: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 18.6 s | 0.49 GB |
| `advance_gather_ihdr` | `advance` in the phase of: gathering IHDR's 13 bytes (`read_ihdr`): no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 22.1 s | 0.57 GB |
| `advance_gather_actl` | `advance` in the phase of: gathering `acTL`'s 8 bytes: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 18.2 s | 0.59 GB |
| `advance_gather_fctl` | `advance` in the phase of: gathering `fcTL`'s 26 bytes (`read_fctl`): no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 13.9 s | 0.57 GB |
| `advance_gather_trns` | `advance` in the phase of: gathering `tRNS`'s 2 or 6 bytes: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 11.6 s | 0.59 GB |
| `advance_gather_fdat` | `advance` in the phase of: gathering `fdAT`'s sequence number: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 11.1 s | 0.58 GB |
| `advance_skip` | `advance` in the phase of: a skipped chunk's data: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 5.6 s | 0.39 GB |
| `advance_palette` | `advance` in the phase of: PLTE's data into the palette: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 6.9 s | 0.39 GB |
| `advance_trns` | `advance` in the phase of: a palette image's `tRNS` data into the palette: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 10.5 s | 0.39 GB |
| `advance_crc_iend` | `advance` in the phase of: IEND's CRC (the end of the stream): no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 7.9 s | 0.39 GB |
| `advance_crc_data` | `advance` in the phase of: an IDAT or fdAT chunk's CRC (which may complete a frame): no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 9.3 s | 0.39 GB |
| `advance_crc_other` | `advance` in the phase of: any other chunk's CRC: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 5.6 s | 0.39 GB |
| `advance_ended` | `advance` in the phase of: after IEND: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 1.6 s | 0.39 GB |
| `advance_spent` | `advance` in the phase of: after an error: no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 1.6 s | 0.40 GB |
| `advance_data_finished` | `advance` in the phase of: IDAT or fdAT data of a frame that is complete (skipped): no panic, at most the input used and at least one byte of a non-empty input, `state_inv` afterwards | any state with the invariant (`Png::state_inv`), 2 by 2 canvas, any buffers, input up to 2 bytes | 3.2 s | 0.39 GB |
| `begin_frame_any` | starting a frame: disposal, the saved canvas, the first pass; `state_inv` afterwards | any state with the invariant and no frame begun, 2 by 2 canvas, any buffers | 63.3 s | 1.57 GB |
| `engine_round_any` | the engine's call of one round of the zlib loop (`feed_once`, part 1): afterwards the invariant holds and the frame is active, or the scanline is full and the state is the one the scanline harnesses assume | any active frame with the invariant, 2 by 2 canvas, any buffers, input up to 2 bytes, an engine that does anything its contract allows | 8.6 s | 0.49 GB |
| `unfilter_row_any` | the filter of a full scanline in `cur` (`finish_row`, part 1): no panic | any active frame with the invariant, rows up to 16 bytes, any buffers | 12.5 s | 0.39 GB |
| `place_row_gray_source` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Gray, blend `Source`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 89.7 s | 2.24 GB |
| `place_row_gray_over` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Gray, blend `Over`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 80.5 s | 2.81 GB |
| `place_row_rgb_source` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Rgb, blend `Source`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 135.6 s | 2.81 GB |
| `place_row_rgb_over` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Rgb, blend `Over`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 144.6 s | 3.34 GB |
| `place_row_indexed_source` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Indexed, blend `Source`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 103.8 s | 2.00 GB |
| `place_row_indexed_over` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Indexed, blend `Over`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 182.6 s | 2.78 GB |
| `place_row_gray_alpha_source` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type GrayAlpha, blend `Source`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 336.0 s | 2.51 GB |
| `place_row_gray_alpha_over` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type GrayAlpha, blend `Over`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 277.4 s | 3.01 GB |
| `place_row_rgba_source` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Rgba, blend `Source`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 146.9 s | 3.20 GB |
| `place_row_rgba_over` | the pixels of a full scanline converted and blended into the canvas (`finish_row`, part 2), colour type Rgba, blend `Over`: no panic | any active frame with the invariant, any depth, tRNS and palette, interlaced or not, any buffers | 229.3 s | 3.07 GB |
| `next_row_any` | the next scanline or pass after a scanline is placed (`finish_row`, part 3, the only part that changes the state): `state_inv` afterwards, frame still active | any active frame with the invariant whose scanline is full, any buffers | 10.8 s | 0.41 GB |
| `round_end_any` | what the engine outcome of a round means (`feed_once`, part 3): `state_inv` afterwards; going on only with the frame active | any active frame with the invariant, any `Progress` and outcome, rest of the input up to 2 bytes | 2.8 s | 0.19 GB |

Written, **not harnesses** (comment blocks in `src/proofs.rs`; the measured outcome, Kani 0.68.0 with its default CBMC settings unless stated):

| Written | Statement | Outcome |
|---------|-----------|---------|
| `adam7_sizes_add_up` | the seven pass sizes add up to `w * h` for every width and height to 2^14 | no verdict in 25 minutes with cadical, kissat or minisat; split on the residues (`w = 8a + 3`, `h = 8b + 5`, `a` and `b` any up to 2047) kissat had none in 10 minutes either: it is a ring identity (seven products against one) |
| the item 6.3 template on the whole `step` | the step function over any state, as GIF's | not attempted (GIF's experience, item 6.7: no verdict); its parts are the harnesses above |

What follows from this, stated plainly:

- **`advance` is proven in every phase and kind of chunk but one case**: the image-data phase (`Phase::Data`) in the stages where a frame is idle or active is not one harness, because it calls `feed`, whose loop has no bound the model checker can unroll (a conforming engine may produce one byte a round). It is covered by its parts, which compose by the structure of the code and not by a machine check: `advance_data_finished` runs `advance`'s own lines of that arm (the CRC update, the counter, the move to the CRC phase) with the frame finished; `image_bytes` is `begin_frame` (`begin_frame_any`) and then `feed`; `feed` is `while feed_once(..)? {}`, and a round (`feed_once`) is `engine_round` (`engine_round_any`), then `finish_row` when the scanline is full (`unfilter_row` and `place_row` take `&self`, so only `next_row` changes the state: `next_row_any`, and the other two are no-panic harnesses), then `round_end` (`round_end_any`). Each part's precondition is the one before it leaves (`engine_round_any` ends in what `next_row_any` assumes, and in what `round_end_any` assumes). A loop cannot be shown by a bounded harness; each round keeping the invariant is the induction step, proven for every round.
- **`step` is `Parts::new` and a loop of `advance`**: that it keeps the invariant across a call follows from `advance` doing, by induction over its calls (argued, as in the original plan; the tests' invariant check exercises it on every step of every stream).
- **The pass sizes summing to `w * h`** is **argued, not machine-checked**: the counting along one axis is (`adam7_axis_split`), and the sum follows from it by three lines of algebra (in `src/proofs.rs`), and also from the bijection the three Adam7 harnesses prove.
- **Tier 1's harness requirement** (CLAUDE.md rule 7: Kani harnesses) **is now met in the sense that every statement the plan names has harnesses that pass locally**: the step function over any state with the invariant and any chunk up to 2 bytes (in parts, with the one composition above), the filters over any row up to 16 bytes, Adam7 over every width and height up to 2^14. The other half of the requirement, **CI's green full verification on a pull request, has not run**, so **the tier stays 0**.

### What the harnesses cover, and what they do not

- **A stand-in engine.** The decoder is generic over the zlib engine (`src/engine.rs`) and the step harnesses use an engine that answers anything the contract allows (any `consumed`, `produced` and bytes, any outcome), so the step harnesses hold for every zlib engine that obeys the contract, not only `clazel-deflate`'s (whose step is tier 0). The window is 0 bytes and the palette 2 entries there, so the work buffer is 57 bytes.
- **A 2 by 2 canvas** in the step harnesses (every colour type and depth, interlaced or not); the filters, Adam7, samples and CRC are over their own ranges as the table says.
- **The template on the whole step is not a harness** (`src/proofs.rs` has its text): GIF's experience (6.7) was that the model checker does not finish it, and it was not tried here. `step` is `Parts::new` and a loop of `advance`, which the `advance_*` harnesses cover phase by phase (the one case, the image-data phase with a frame idle or active, is covered by its parts, above), so the step's statements follow from the parts by induction over calls, argued and not machine-checked.
- **What Kani found.** `state_inv` was too weak in the gather phase: a chunk that is gathered (IHDR, `acTL`, `fcTL`, `tRNS`, `fdAT`) may have more data than is gathered only for `fdAT` (its image data follows the sequence number), and IHDR is only gathered before anything is read. `advance_gather_*` failed on states the invariant allowed but `chunk_start` never makes; the invariant now says what `chunk_start` establishes (`advance_header` proves it does), and all 26 tests, which check it on every step, still pass.
- **What the tests' invariant check found** (not Kani): a `tRNS` chunk of the wrong length for colour type 0 or 2 left the state in an impossible phase; fixed (the length is checked at the chunk header). `PLTE` entries past the palette's capacity are not stored (`palette_len` is clamped), which makes the invariant true for the proofs' 2-entry palette too.
- By induction over steps, as the plan says (argued, not machine-checked): `Png::inv` holds after `start` and each step keeps it.

## Tests (`tests/conformance_png.rs`, `tests/common/mod.rs`)

`tests/data/pngsuite/` (PngSuite, 2017-07-19 archive, 176 files, its own permissive notice, through `cargo xtask testdata`'s converter `pngsuite`) and streams made by `tests/common` against the `png` crate 0.18.1, **exact on every frame's RGBA8**; in a native debug run:

| Suite | Result |
|-------|--------|
| PngSuite differential | 176 of 176: the 14 `x*` files refused by both decoders, the other 162 equal pixel for pixel |
| PngSuite chunking (1, 2, 3, 7, 64, 4096 bytes, with and without empty chunks) | 176 of 176 equal to the whole-file decode, invariant checked on every step |
| PngSuite mutations (60 per file, half with every CRC rewritten) | 9,720 mutants of the 162 valid files: no panic, invariant kept, two chunkings agree; 611 accepted by both and equal; **0 accepted by ours and refused by `png`**; 498 accepted by `png` only (our CRC and chunk-rule strictness, listed) |
| Generated images | 1,080 of 1,080: every colour type and depth, interlaced or not, sizes 1 to 9 on a side, filters, `tRNS`, palettes, IDAT pieces, ancillary chunks |
| `png` encoder streams | 60 of 60 (compressed, every filter and level) |
| Animations | 600 of 600: random APNG frames, every dispose and blend, composited against the test's own reference |
| By hand | 180 chunk-grammar and refusal cases, 25 APNG cases, 17 listed-choice pixel checks, size limits (16,384 on a side, 2^26 pixels), every prefix of two streams |

A finding about the reference: `png` 0.18.1 writes an **interlaced APNG frame narrower than the canvas with the canvas's stride** (`next_frame` gives `expand_pass` the image's width, not the frame's), so its frame buffers are spread out; the test's adapter reads each pixel from where `png` put it. Not reported upstream (CLAUDE.md rule 9: a human does that).

**Miri** (nightly-2026-08-21, in WSL, the xtask command, virtual clock): the first full run passed all 26 tests but 5 took over the 300 s limit (animations 323 s, encoder 309 s, chunking 850 s, differential 690 s, mutations 778 s; the rest under 136 s). Timing each test natively with the Miri branch forced on had suggested 0.04 s a test would be about a minute: it was about 20 times worse (Miri's ratio on this code is about 25,000, not 1,600; the 200 KiB engine state and 32 KiB window are cleared for every decode). The strides were then cut by 2 to 5 times (differential every 24th of the 88 small files, chunking every 50th at chunk size 1 only, mutations every 48th, 3 animations, 1 encoder stream) and the Miri run was **not repeated** (WSL kept restarting), so the new strides' times are estimates (about 170 to 200 s for the three PngSuite suites, 120 s for animations, 60 s for the encoder).

## Not done

- Looping (`num_plays`) and frame timing policy (the `delay_den` of 0, a
  floor for short delays) are `clazel-image`'s and item 6.19's; animation is
  decoded but nothing displays more than the first frame yet.
- No colour management (listed), no `eXIf`, `bKGD`, `sBIT` or text use.
- `clazel-deflate`'s `Inflater::step` is not proven (its tier is 0; its
  README says what is), so the PNG proofs hold for any engine obeying
  `Engine`'s contract, and the real engine's obedience rests on its tests.
- The tier stays 0 until CI's full verification has run the harnesses green
  and the rest of Tier 1 (CLAUDE.md rule 7).
