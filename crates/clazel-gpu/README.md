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

One harness per process, each with a 20-minute and 8 GB cap.

| Harness | Covers | Time | Peak memory |
|---------|--------|------|-------------|
| `place_any` | every input | | |
| `grown_capacity_any` | every input | | |
| `texel_index_any` | every input | | |
| `rect_at_any` | every input | | |
| `intersect_any` | every input | | |
| `blend_any` | every input | | |
| `clip_then_draw_any` | one step from any state, any viewport | | |
| `atlas_upload_any` | bounded: two live masks, masks up to 2 × 2 | | |

## Miri

| Test | Time under Miri |
|------|-----------------|

## What is left of item 5.17b

- **The Metal backend.** Blocked on a question for the maintainer (below). Its design:
  `MTLCreateSystemDefaultDevice`, one command queue, the library compiled at start
  from `quad.metal` (embedded at build time; the machine has no offline Metal
  toolchain), one render pipeline blending one / one minus source alpha into
  `RGBA8Unorm`, the target a texture on an IOSurface the backend creates
  (`IOSurfaceCreate`), the quads and each upload copied by `newBufferWithBytes`
  (each is one audited call that copies), uploads as blit copies ordered with the
  draws, scissors by `setScissorRect:`, and the pixels read by `getBytes:` for the
  tests. Every list item is to be tested against stored pixels and the reference,
  skipping with a printed reason where there is no device.
- **The Vulkan backend** (Linux, lavapipe in CI). It needs: `clazel-sys` linking only
  `libvulkan`; hand-written `#[repr(C)]` structures checked against the
  specification; the checker taught to accept a call through a function pointer
  looked up with `vkGetDeviceProcAddr` (for `VK_KHR_external_memory_fd` and
  `VK_EXT_external_memory_dma_buf`); no WSI extension; the SPIR-V committed here; and
  the rows copied into a mapped buffer by one audited call.
- **The Direct3D 12 backend** (Windows, WARP as fallback). It needs: the checker
  taught to accept a COM call through a vtable, with hand-written vtable declarations
  audited against the headers; the shaders stored compiled for Direct3D (DXBC, unless
  the prototype finds DXIL's signing workable) with a check like the SPIR-V one;
  presenting with `CreateSwapChainForCompositionSurfaceHandle`, with no window.
- **Neither can run on the development machine** (an Apple-silicon Mac).

## The question for the maintainer

The plan reaches Metal through several `#[link_name = "objc_msgSend"]` declarations,
one per message signature (items 5.17b and 5.21). That does not build: rustc's
`clashing_extern_declarations` lint, a warning by default, fires on the second
declaration of the same symbol with another signature (measured on 1.98.1), and CI
denies warnings. Every way round it changes the audit rule:

1. **Typed function pointers** (recommended): declare `objc_msgSend` once and give
   each signature a `const` function pointer made by `transmute` of it, which is the
   cast Apple's documentation prescribes for calling `objc_msgSend`. The checker would
   accept exactly that form (a listed name, the one source, a function-pointer type)
   and calls through the listed names. Vulkan needs the same form for
   `vkGetDeviceProcAddr`, which the plan already asks for. It changes the wording of
   CLAUDE.md rule 1 ("one call to a foreign function"), so it is not decided here.
2. Allow `clashing_extern_declarations` in `clazel-sys`'s manifest, which weakens a
   lint (CLAUDE.md rule 2).
3. Assembly trampolines under distinct symbols, a new kind of code to audit.
