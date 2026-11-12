# clazel-gpu

The GPU process's drawing for [Clazel](../../README.md), a web browser whose parsers
of untrusted input carry machine-checked proofs. Phase 5 item 5.17b
(`docs/phases/phase-5.md`): a display list and a viewport to pixels, on the GPU,
through fixed pipelines, with backends below a small trait. Tier 0, as the plan
places it: a GPU driver is in this process's trusted base whatever is proven here.

The list comes from a renderer the GPU process must assume is compromised.
`Gpu::draw` takes the list's bytes and passes them through `clazel-displaylist`'s
decoder and validator (item 5.17a) before anything here reads them, and
`theorem_validated_bounds` is all this crate relies on. Every step is still checked
and fails with an `Error` rather than a panic; any error ends the GPU process, and
what happens next is item 5.17c's.

## What is built

- **The shared batching** (`src/batch.rs`): a validated list and a viewport to a
  `Frame` of operations in order: atlas replacements, atlas uploads, and draws of
  quads under a scissor rectangle. Consecutive draws under one scissor are one batch.
- **The glyph atlas** (`src/atlas.rs`): one linear GPU buffer of coverage bytes, a
  bump allocator, compacted when full.
- **The backend trait** (`src/backend.rs`) and the quad format the shaders read.
- **A fake backend** (`src/soft.rs`, `SoftBackend`): runs a frame in software as the
  shaders would, with no foreign call. Miri runs the batching through it.
- **The software reference** (`src/reference.rs`): the pixels a list means, computed
  straight from its items, sharing nothing with the batching or the fake backend but
  the blending rule and the rectangle type.
- **Test scenes** (`src/scenes.rs`): every list item (fill, clip push and pop, mask
  upload, draw and free), masks carried between lists, a cleared frame, and a
  compaction in the middle of a list. `src/tests.rs` draws each through the decoder,
  the validator, the batching and the fake backend, and requires the reference's
  pixels exactly.
- **The shaders** (`shaders/`): `quad.metal` in the Metal Shading Language, and
  `quad.vert` and `quad.frag` in GLSL 4.50 for Vulkan, compiled to the committed
  `quad.vert.spv` and `quad.frag.spv` by `naga` in `xtask` (tooling, never shipped).
  `cargo xtask tables` writes the SPIR-V and `cargo xtask check` fails if it differs
  from what the GLSL compiles to. The MSL was compiled once by Metal on this machine
  (Apple M1 Pro) with a throwaway script; nothing in the repository runs it yet.
- **Kani harnesses** (`src/proofs.rs`), listed below.

## Decisions

Taken from the plan (item 5.17b's listed choices, 5.0(d) and (e)) and recorded here,
as the plan asks. Each is also written where it is made.

- **Blending**: source-over in 8-bit sRGB, premultiplied, with no gamma correction
  (the plan's listed choice). The software rule is the exact value rounded once:
  `c·k/255 + d·(1 − a·k/255²)` in levels, halves up, clamped to 255. A GPU blends in
  floating point and may differ by one level; the backend tests compare with the
  reference within one level per channel and with stored pixels exactly.
- **Colours have no rule** in a list, so a channel may exceed its alpha; the result
  clamps at 255, as an unsigned normalized target does.
- **Whole pixels**: items have integer device-pixel bounds (5.16), so nothing is
  antialiased but masks, whose coverage is in their bytes.
- **Clips are scissor rectangles** (the plan). Quads are cut to the viewport on the
  CPU, so the shaders see small integers, and not to the clip. Nothing is drawn under
  an empty clip.
- **One pipeline, one quad per item**: a fill is a quad with full coverage, a mask a
  quad reading the atlas. Quads are 9 words read by instance index, coverage one byte
  read by pixel, so there is no vertex format, no sampler and no texture coordinate.
- **The atlas is linear**, not a 2D texture: a mask is `columns × rows` bytes at an
  offset, in a slot padded to whole 4-byte words (Metal's buffer copies on macOS need
  that). Allocation is one-dimensional, a compaction always fits (at most 64 MiB of
  coverage are live, the validator's limit, in at most 65,536 slots, and the store
  grows to 128 MiB), and every mask shares
  one store, so masks of every id draw in one batch. A copy of each live mask stays on
  the CPU (at most 64 MiB) for compaction.
- **The shaders bound their own reads** (an instance past `quad_count` draws nothing;
  a coverage index past `atlas_bytes` reads 0), and the SPIR-V is compiled with
  `naga`'s bounds checks on every buffer read as well. Rust's types cannot check what
  a shader reads; this, the batching that sets the counts, and the tests are the
  evidence.
- **Each frame starts from transparent black**; the list paints the canvas.
- **The viewport** is 1 to 8192 device pixels a side.
- **One frame at a time**, finished before `Gpu::draw` returns.
- **A hostile renderer can make its own GPU process slow** (forcing a compaction per
  upload near the 64 MiB limit, or sending a large list). That only slows its own
  tab, which a large list already can.
- **The target is the backend's** until item 5.18 builds the ring of shared buffers:
  each backend draws into a buffer it creates itself, behind `Backend::read_pixels`,
  so 5.18 can hand a backend its buffers instead without a change above the trait.
- **Placement in the status image**: the GPU process is placed with the renderer
  (`PLACES` in `xtask/src/status.rs`), sandboxed and one per tab like it; the detail
  image has no GPU-process panel yet (item 5.27).

## Kani

Each harness in its own process group, with a 20-minute and 8 GB cap polled every
5 s (`src/proofs.rs`). Times are the whole `cargo kani` run with the crate already
built; peak memory below 0.01 GB means the run ended before the first poll.

| Harness | Covers | Result | Verification time | Wall time | Peak memory |
|---------|--------|--------|-------------------|-----------|-------------|
| `place_any` | every input | passed, 10 checks | 0.09 s | 12 s | 0.67 GB |
| `grown_capacity_any` | every capacity the atlas holds, any total | passed, 63 checks | 0.28 s | 3 s | < 0.01 GB |
| `rect_at_any` | every input | passed, 77 checks | 0.35 s | 2 s | < 0.01 GB |
| `intersect_any` | every input | passed, 14 checks | 0.16 s | 1 s | < 0.01 GB |
| `blend_any` | every input | passed, 20 checks | 0.99 s | 2 s | < 0.01 GB |
| `visible_any` | every input (the draw step's cut) | passed, 15 checks | 0.33 s | 2 s | < 0.01 GB |
| `clip_then_draw_any` | one draw from a fresh frame, any viewport, clip and quad | passed, 696 checks | 2.5 s | 5 s | < 0.01 GB |

Proved for every size: `place`, `grown_capacity`, `Rect::at`, `Rect::intersect`,
`blend`, `batch::visible`. Bounded: the builder, to one draw from a fresh frame.

Not covered, each removed at a cap:

| Harness | Cap | What covers it instead |
|---------|-----|------------------------|
| `texel_index_any` (any `u16` sides; then sides up to 2048) | 20 min twice, 0.17 GB | unit tests, every scene; all its steps are checked |
| `atlas_upload_any` (two live masks of up to 2 × 2, any offsets) | 8 GB in 83 s | `atlas.rs` tests, `a_compaction_closes_the_open_batch`, scene "atlas" |
| `clip_then_draw_any`, first form (a draw, then a clip and a draw) | 8 GB in 21 s | split into `visible_any` and the one-draw form above |

## Miri

Each test in its own process with a 10-minute cap, times on Miri's clock
(`--report-time`). The fake backend makes no foreign call, so the whole batching
runs under Miri; the Metal tests (`tests/metal.rs`, and `clazel-sys`'s
`a_surface_texture_has_the_surface_size`) call the GPU and are ignored under Miri.

| Test | Time |
|------|------|
| `tests::scene_atlas` | 55.9 s |
| `tests::scene_masks` | 39.2 s |
| `tests::scene_clips` | 30.7 s |
| `tests::scene_fill` | 27.5 s |
| `tests::scene_frames` | 18.3 s |
| `tests::bad_lists_are_refused_before_drawing` | 14.5 s |
| `soft::tests::blending_is_the_exact_value_rounded` | 12.6 s (290 s before its Miri inputs were thinned) |
| `tests::every_scene_is_tested` | 0.8 s |
| `batch::tests::a_compaction_closes_the_open_batch` | 0.1 s |
| the other 15 unit tests | under 0.05 s each |
| `clazel-sys` `macos::metal::tests::sizes_are_checked_before_any_call` | 0.001 s |

## The Metal backend

`src/metal.rs`, macOS on Apple silicon only, through `clazel_sys::macos::metal`
(every foreign call is there, under CLAUDE.md rule 1). The shaders are compiled at
start from `quad.metal` as embedded at build time (the machine has no offline Metal
toolchain); one command buffer per frame holds uploads as blit copies from a staging
buffer and render passes between them, under scissors, into a texture on an IOSurface
the backend makes (`Target`, which item 5.18 can supply instead); the frame is
committed and waited for. Any nil, failed compile or command buffer error is a
`BackendError`.

`tests/metal.rs` draws every scene and compares each list's pixels with the software
reference (within one level per channel) and with the stored pixels in
`tests/pixels/` (exactly). On the development machine (Apple M1 Pro, macOS 26) every
channel of every scene equals the reference: the largest difference is 0. A mutant
shader with full coverage for every mask fails both comparisons. The test binary
writes what it ran on once (`clazel-gpu: Metal device "<name>"`, the name from the OS,
since the `clazel-sys` wrappers cannot read the device's own name without new foreign
calls), straight to standard error so that libtest does not capture it and the line
is in CI's log for passing tests too.

Without a usable Metal device the tests skip with a logged reason (`clazel-gpu:
skipped: …`, written the same way) on a developer's
machine, but fail when the `CI` environment variable is set: CI's `macos-15` runner
(Apple silicon, virtualised) is expected to offer a paravirtual Metal device, and the
first CI run settles whether it does. So far the tests have run only on the
development machine. A paravirtual device may behave differently (IOSurface-backed
textures, the blit path, rounding), so a failure there is possible and would be real
information, not noise.

## What is left of item 5.17b

- **The Vulkan backend** (Linux, lavapipe in CI). It needs: `clazel-sys` linking only
  `libvulkan`; hand-written `#[repr(C)]` structures checked against the
  specification; extension functions (`VK_KHR_external_memory_fd`,
  `VK_EXT_external_memory_dma_buf`) looked up with `vkGetDeviceProcAddr`, which needs
  the checker's dispatcher casts (below) extended to a second kind of dispatcher, a
  looked-up pointer rather than a symbol, decided when that backend is built; no WSI
  extension; the SPIR-V committed here; and the atlas uploads as buffer copies like
  Metal's, or rows copied into a mapped buffer by one audited call.
- **The Direct3D 12 backend** (Windows, WARP as fallback). It needs: the checker
  taught to accept a COM call through a vtable, with hand-written vtable declarations
  audited against the headers; the shaders stored compiled for Direct3D (DXBC, unless
  the prototype finds DXIL's signing workable) with a check like the SPIR-V one;
  presenting with `CreateSwapChainForCompositionSurfaceHandle`, with no window.
- **Neither can run on the development machine** (an Apple-silicon Mac).
- **Intel Macs** are not supported by the Metal backend (shared-storage textures and
  `BOOL` as `bool` are Apple silicon's).
- **The shared buffers and the process boundary** are items 5.18 and 5.21a.

## How Metal is reached: dispatcher casts

The plan reached Metal through several `#[link_name = "objc_msgSend"]` declarations,
one per message signature (items 5.17b and 5.21). That does not build: rustc's
`clashing_extern_declarations` lint, a warning by default, fires on the second
declaration of the same symbol with another signature (measured on 1.98.1), and CI
denies warnings. The maintainer delegated the choice, and the form taken is:
`objc_msgSend` is declared once, with no parameters, and each signature is one
`const` holding one `std::mem::transmute` of it to an `unsafe extern "C-unwind"
fn(..)` type, which is the cast Apple's documentation prescribes. `xtask/src/sys.rs`
accepts exactly that form and rejects every other `transmute`, use of the
dispatcher, or call through a pointer. It changes the wording CLAUDE.md rule 1
needs, which is proposed for the maintainer, not made here.

The dispatcher and its casts are `"C-unwind"`, and the checker accepts no other ABI
for them. Metal raises Objective-C exceptions for API misuse, which the wrappers'
checks are there to rule out; should one be thrown anyway, it unwinds through the Rust
frames above the call as a foreign exception, which the Rust reference defines
(`items.fn.extern.unwind.behavior`: destructors run under `panic=unwind`, the process
aborts under `panic=abort`), where through an `extern "C"` cast it would be undefined
behaviour (`panic.unwind.ffi.undefined`). Nothing catches it: an exception is a bug
the GPU process may die of. An open encoder is still ended on the way out, by a guard
whose `Drop` sends `endEncoding`.
