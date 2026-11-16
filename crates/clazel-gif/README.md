# clazel-gif

A GIF decoder for [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs. Phase 6 item 6.7
(`docs/phases/phase-6.md`). It runs in the renderer's sandbox, on bytes a
page chose, and implements the one interface of every Phase 6 decoder,
`clazel_image_shape::Decoder` (item 6.3): a resumable step function over
caller-owned buffers, nothing allocated while decoding.

Its only dependency is `clazel-image-shape`. The `gif` crate is a
dev-dependency, used only by the differential test.

## What it does

GIF89a (CompuServe, 1990; GIF87a streams too): header, logical screen
descriptor, global and local colour tables, image descriptors, interlacing
(Appendix E), variable-code-size LZW (Appendix F), the Graphic Control
Extension (disposal, delay, transparent index), every other extension
skipped by its sub-block sizes, the trailer. **Every frame** is decoded and
composited onto the canvas with the previous frame's disposal method; after
each `Status::FrameDone` the pixel buffer holds the canvas as displayed
with that frame, and `Gif::frame()` has the frame's delay, disposal and
rectangle. The first `FrameDone` is the first composited frame that
decision 6.0(d)'s option A shows. A 1 by 1 `s.gif`, which Hacker News uses
for spacing, is one of the test files.

| File | Holds |
|------|-------|
| `src/lib.rs` | the pinned standard, the section numbers, the listed choices |
| `src/decoder.rs` | the state machine over the blocks, `Gif`, `Decoder`, `Gif::inv` |
| `src/lzw.rs` | LZW: clear, end, full-table behaviour, the three arrays |
| `src/sink.rs` | colour indexes to canvas pixels: palette, interlace, clipping |
| `src/work.rs` | the layout of the work buffer |
| `src/proofs.rs` | the Kani harnesses |

The work buffer is `work_len(config)` = 17,920 bytes (two colour tables of
768, LZW's prefix, suffix and stack arrays for 4096 codes) plus a copy of
the canvas (for disposal method 3), so a decode needs the pixel buffer
twice over plus 17 kB. That copy is a listed choice (`src/work.rs`); a
caller bounding memory counts it.

## Listed choices (`src/lib.rs` has them with the section numbers)

Canvas transparent black at the start, background colour ignored, disposal 2
to transparent; disposal 4 to 7 read as 0; frames outside the canvas
clipped; a colour index past the table draws nothing; the LZW full table
keeps decoding ("deferred clear") with no new entries until a clear code;
minimum code sizes 2 to 8; too little or too much image data tolerated; a
malformed Graphic Control Extension skipped; no resynchronisation after an
unknown block; the trailer is `NoMoreFrames`; the NETSCAPE2.0 loop count is
not read (6.19's policy).

## Kani harnesses (`src/proofs.rs`)

| Harness | Statement (every one: no panic, no overflow, no out-of-bounds index) | Bound |
|---------|-----------|-------|
| `control_byte_any` | one byte in any phase but image data: the invariant holds afterwards on `Ok` | any state with `Gif::inv`, any buffer contents; 2 by 2 canvas, LZW at 3 bits |
| `data_byte_any` | one byte of image data (LZW through the colour table onto the canvas): the invariant holds afterwards on `Ok` | the same |
| `lzw_any` | one byte of LZW, up to three codes, over **any contents** of the three arrays and a sink that answers anything: `Lzw::inv` kept on `Ok(More)` | any state with `Lzw::inv`; 3 bits (8 entries) |
| `lzw_code_any` | one code: the table part of the invariant kept, at most `2^4` indexes out | any state with `Lzw::inv`, any arrays, any code of `code_size` bits; 4 bits (16 entries), so a code size of 3 grows to 4 |
| `sink_put_any` | one index through the palette onto the canvas: `Sink::inv` kept, nothing written outside the canvas, `remaining` down by one | any state with `Sink::inv`, a frame of any position and size, palette of up to 4 entries, canvas up to 2 by 2 |
| `interlace_row_any` | the next interlaced row stays in a pass of 0 to 3 and in the frame or ends it | **every** `u16` height, any row and pass |
| `interlace_covers_frame` | an interlaced frame receives its indexes into every pixel exactly once | every width and height up to 4 by 4 |

Run in WSL Ubuntu with Kani 0.68.0 (`cargo kani -p clazel-gif`): 7 harnesses, 7 pass, 0 fail: `interlace_covers_frame` 54 s, `interlace_row_any` 0.1 s, `sink_put_any` 2 s, `lzw_any` 46 s, `lzw_code_any` 23 s, `data_byte_any` 159 s, `control_byte_any` 7 s. A mutated `Lzw::add` (the code size allowed one bit too far) fails `lzw_code_any`. Not run: the template on the whole step (below).

The harnesses were committed (statements, the invariant, stubbed bodies)
before the implementation, in their own commit.

### What Kani covers, and what it does not

- **The step function itself is not machine-checked, its two halves are.**
  Item 6.3's template, `decoder_step_harness!`, expands and runs from this
  crate (it was instantiated on the stub first, and failed as it should
  against it), but on the whole of `Gif::step` the model checker passed 6 GB
  after 5.5 minutes on an 8 GB machine and was stopped, so that harness is
  not here (`src/proofs.rs` has its text). `step` is `Parts::new` (the
  buffers' lengths are in `inv`, and `src/work.rs` has a unit test), then a
  loop of `byte`, which hands image data to `data_byte` and everything else
  to `control_byte`, stopping at the first frame, error or trailer and
  returning the index it stopped at as `consumed`. Those two functions are
  the harnesses `control_byte_any` and `data_byte_any`, each for any state
  with the invariant. What the template would add, and is argued here, not
  proven: that `step` keeps `inv` over **several** bytes (it follows by
  induction from one byte keeping it), that `consumed <= chunk.len()` and
  `NeedMore` consumes the whole chunk (a loop's index, read from the
  code), and that a stray write outside the buffers is impossible (safe
  Rust bounds-checks every index, and Kani proves none panics).
- **Small tables.** The LZW table has 4096 entries and walking a prefix chain
  is a loop over symbolic arrays that a model checker does not finish. The
  decoder is generic over the code size, `Lzw<BITS>`, and the browser uses
  12; the harnesses of the decoder run at 3 bits (8 entries, `TABLE_BITS`
  under `cfg!(kani)` in `src/lzw.rs`) and `lzw_code_any` at 4. The code is
  the same code with another constant. Every table access is checked
  and every loop has a constant bound (a chain is followed at most
  `TABLE_LEN` steps, a byte yields at most three codes, argued in the
  comment at that loop), so the 12-bit table adds no kind of access that
  the 3-bit one lacks: that is an argument, not a machine-checked fact. The
  unit tests, the differential test and Miri run the real size.
- **A 2 by 2 canvas** in the decoder's harnesses, any size in the sink's
  (up to 2 by 2) and interlace's (every height). The colour tables are the
  real 768 bytes each.
- **Why separate arrays**: the byte harnesses give the decoder its parts as
  separate arrays rather than one work buffer cut by `Parts::new`; the model
  checker follows every access into one 1.6 kB object. And they use the
  `kissat` solver: with the default one CBMC ran out of memory on
  `data_byte_any`.
- **By induction over steps** (as the plan says, argued here and not
  machine-checked): `Gif::inv` holds after `start` and before the first
  `step` (it is true of `start`'s state and of the buffers `Buffers::new`
  cuts), and each byte harness proves one byte keeps it, so it holds at
  every byte of every input of every length.
- **Not stated**: that the pixels are right (the differential test's and the
  hand-made cases'), that the work is bounded in time (a frame claiming
  65535 by 65535 pixels is decoded as far as its data goes, clipped to the
  canvas), and that every state `inv` admits is reachable (it
  over-approximates, so the harnesses are sound).
- The tier stays 0 until CI's full verification has run these green
  (CLAUDE.md rule 7).

## Tests (`tests/conformance_gif.rs`)

Wuffs' GIF test data (`tests/data/wuffs-gif*`, commit `b36a81d`, MIT or
Apache-2.0 at our choice, through `cargo xtask testdata`'s converter) against
the `gif` crate 0.14.2, **exact on every frame's composited RGBA**: 25 of 31
files agree, 6 differ in listed choices, each with its reason in the test.
Every file at chunk sizes 1 to 4096 equals the whole-file decode, with the
invariant checked on every step. Deterministic byte mutations of every file
never panic (9,653 mutants). 62 GIFs made by hand cover disposal,
transparency, local tables, clipping, extensions, interlacing at every
height from 1 to 40 and a real LZW encoder through every minimum code size.
Under Miri the suites run on the files of at most 16 KiB, chunk sizes 1 and
4096, and 4 mutations each.

## Not done

Looping (the NETSCAPE2.0 count) and frame timing policy (browsers' 100 ms
floor for delays under 20 ms) are `clazel-image`'s and item 6.19's. Animation
is decoded but nothing displays more than the first frame yet.
