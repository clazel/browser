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

Eight harnesses, all passing: `cargo kani -p clazel-png` ends in `8 successfully verified harnesses, 0 failures` (Kani 0.68.0, macOS arm64, about 2 minutes in all; the time column is each harness's own verification time on that machine). Every one is also a no-panic, no-overflow, no-out-of-bounds proof for the code it runs.

| Harness | Statement | Bound | Local time |
|---------|-----------|-------|-----------|
| `paeth_is_the_spec` | the Paeth predictor equals 9.4's formula in `i32` | every `a`, `b`, `c` | 1.9 s |
| `unfilter_any` | all five filters equal 9.2's formulas byte by byte, a type above 4 is refused | any row up to 8 bytes, `bpp` 1 to 8 (`filter_bpp()` is `.max(1)` and is the only caller, `src/decoder/image.rs`; 9.2 rounds bpp up to 1), any `filter` byte | 52.0 s |
| `adam7_pixel_in_one_pass` | every pixel is in exactly one pass, at the coordinates the pass gives back, inside the pass's size | **every** width and height 1 to 2^14 | 0.6 s |
| `adam7_pass_pixels_in_image` | every pass pixel is inside the image | the same | 0.3 s |
| `adam7_whole_image` | a non-interlaced image is one pass, the whole image; pass 1 of it and pass 7 of an interlaced one do not exist | the same | 0.07 s |
| `sample_and_rgba_any` | `sample`, `rgba`, `over` (and `over`'s two identities) | every colour type, depth, index, `tRNS`, palette up to 8 bytes, row up to 8 bytes | 4.9 s |
| `crc_update_any` | the CRC update | any register, up to 2 bytes | 0.7 s |
| `begin_frame_any` | starting a frame: disposal, the saved canvas, the first pass; `state_inv` afterwards | any state with the invariant, 2 by 2 canvas, any buffers | 39.8 s |

Written, **not harnesses** (each is a `// NOT a harness:` comment block in `src/proofs.rs`, because a harness that gives no verdict is not a proof; the measured outcome, Kani 0.68.0 with its default CBMC settings unless stated):

| Written | Statement | Outcome |
|---------|-----------|---------|
| `adam7_sizes_add_up` | the seven pass sizes add up to `w * h` for every width and height to 2^14 | no verdict in 25 minutes with cadical, kissat or minisat |
| `control_any` | `advance` in every phase but image data: uses 1 byte to all of a non-empty input, `state_inv` afterwards | about 10 GB, no verdict in 25 minutes |
| `feed_any` | the zlib loop over an active frame with an engine that does anything its contract allows | about 6.7 GB, no verdict in 25 minutes |
| `data_any` | `advance` in the image-data phase | about 5.6 GB, no verdict in 25 minutes |
| `finish_row_any` | a complete scanline of any content, unfiltered and placed, `state_inv` afterwards | **failed** an unwinding assertion in `unfilter`'s loop (`src/filter.rs:50`) at `unwind(10)` after 305 s and 7.1 GB: its rows are up to 16 bytes, so it needs an unwind of 18 or more; not re-run at that bound |

What follows from this, stated plainly:

- The pass sizes summing to `w * h` is **argued, not machine-checked**: it follows from the bijection the three Adam7 harnesses prove (every pixel in exactly one pass at the position the pass gives back, every pass pixel in the image), and `adam7_sizes_add_up` would state it directly.
- That `advance`, `feed` and `finish_row` keep `state_inv` is **not proven**: only `begin_frame` is. That it holds across a whole `step` is argued by induction over steps (below) and exercised by the tests' invariant check, not shown by Kani.
- **Nothing here claims Tier 1**; the tier stays 0.

### What the harnesses cover, and what they do not

- **A stand-in engine.** The decoder is generic over the zlib engine (`src/engine.rs`) and the step harnesses use an engine that answers anything the contract allows (any `consumed`, `produced` and bytes, any outcome), so a proof of the step (`feed_any` would be one) would hold for every zlib engine that obeys the contract, not only `clazel-deflate`'s (whose step is tier 0). The window is 0 bytes and the palette 2 entries there, so the work buffer is 57 bytes.
- **A 2 by 2 canvas** in the step harnesses (every colour type and depth, interlaced or not); the filters, Adam7, samples and CRC are over their own ranges as the table says.
- **The template on the whole step is not a harness** (`src/proofs.rs` has its text): GIF's experience (6.7) was that the model checker does not finish it, and it was not tried here. `step` is `Parts::new` and a loop of `advance`, which `control_any` and `data_any` would cover for any state with the invariant, but neither finished (table above), so the step's statements are argued, not proven.
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
