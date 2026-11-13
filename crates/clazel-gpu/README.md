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
what happens next is the crash policy's (item 5.17c, below).

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
- **Item 5.17c** (its own section below): the driver blocklist (`data/blocklist`,
  `src/blocklist.rs`), the start that checks it before any list (`src/start.rs`,
  `Gpu::start`), and the crash policy for the kernel (`src/policy.rs`).

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

- **The Vulkan backend's buffer export.** The backend itself is built
  (`src/vulkan.rs`, "The Vulkan backend" below). What is left is the plan's
  zero-copy route: extension functions (`VK_KHR_external_memory_fd`,
  `VK_EXT_external_memory_dma_buf`) looked up with `vkGetDeviceProcAddr`, which
  needs the checker's dispatcher casts (below) extended to a second kind of
  dispatcher, a looked-up pointer rather than a symbol. Today the target is read
  back and its pixels are copied to the host (`src/channel.rs`).
- **The Direct3D 12 backend** (Windows, WARP as fallback). It needs: the checker
  taught to accept a COM call through a vtable, with hand-written vtable declarations
  audited against the headers; the shaders stored compiled for Direct3D (DXBC, unless
  the prototype finds DXIL's signing workable) with a check like the SPIR-V one;
  presenting with `CreateSwapChainForCompositionSurfaceHandle`, with no window.
- **Neither can run on the development machine** (an Apple-silicon Mac).
- **Intel Macs** are not supported by the Metal backend (shared-storage textures and
  `BOOL` as `bool` are Apple silicon's).
- **The shared buffers and the process boundary** are items 5.18 and 5.21a.
- **`Gpu::new` is gone** (item 5.17c): `Gpu::start` checks the blocklist first.

## Item 5.17c: software fallback, driver blocklist, crash policy

A machine with a missing, blocked or crashing driver must still show pages. What is
built here, and what waits for other items:

- **The blocklist** (`data/blocklist`, `src/blocklist.rs`): the table ships embedded
  in the GPU process and starts empty; an entry is added only when a real failure is
  recorded, with a link to the evidence. It is never updated remotely, and nothing is
  reported to any server. The format and its parser are ours (rule 8).
- **The checked start** (`src/start.rs`, `Gpu::start`): the only way to make a
  `Gpu`. It reads the backend's adapter (`Backend::adapter`) and checks it against
  the table before any list is read, and answers `Ready { software }` (item 5.18's
  `GpuReady`) or a `Refusal` (`GpuRefused`, or an exit for a wrong start).
- **The crash policy** (`src/policy.rs`): the item's four rules as a pure state
  machine over the kernel's events, with its numbers stated once (`WINDOW_MS` five
  minutes, `EXITS` and `SITES` three). The plan puts it in the kernel, proven; the
  kernel has no GPU process until item 5.18, so it is built here with no dependency,
  for 5.18 to take over (below).
- **The software path is the same code on a software driver** (5.0(d): no second
  drawing backend): lavapipe on Linux, WARP on Windows. `SoftBackend` stays a test
  double and is never a fallback. lavapipe is reached through the Vulkan backend
  (`clazel-gpu --software`, `browse --gpu=software`, or by itself when the loader
  lists no other device); WARP waits for the Direct3D 12 backend.

### Decisions

Taken from the plan (item 5.17c, 5.0(d), 5.21a) where it was silent; each is also
written at the top of the file that makes it.

- **The table's format** (`src/blocklist.rs`): one entry per line, `<api> <vendor>
  <device> <drivers> <evidence> <reason>`, printable ASCII and LF only; `api` is
  `vulkan`, `d3d12` or `metal`; ids are `0x` and 1 to 8 hex digits, the device may
  be `*`; `drivers` is `*`, one version or `first-last`; `evidence` starts
  `https://`; the reason is the rest of the line. At most 64 KiB, 1,024 bytes a
  line and 1,024 entries. Every error names its line.
- **Versions are four 16-bit parts**, compared in order: Direct3D's driver version
  exactly. Parts left out are 0 in `first` and 65,535 in `last`, so `470-470.57`
  covers every 470.57.x. Vulkan's `driverVersion` is encoded per vendor, and its
  backend will decode it into parts.
- **An unknown driver version matches only `*`**: an entry with a range is for
  measured versions, and refusing a device whose version cannot be read would block
  it on a guess.
- **Software adapters are never checked**: the software driver is the fallback, and
  the one CI tests.
- **An unreadable table refuses the device** (fails closed, as `GpuRefused`); a unit
  test parses the shipped table, so no shipped build reaches it.
- **Metal is described as Apple's vendor id, no device id, no driver version.**
  Apple silicon has no PCI device id, and the `clazel-sys` wrappers read neither the
  device's name nor the OS version without new foreign calls, which this item does
  not add (`clazel-sys` is unchanged). A Metal entry can only use `*` for device and
  drivers; with no fallback on macOS, a refused Metal device shows the notice.
- **The kernel chooses the mode.** A process started for hardware that finds only a
  software adapter draws with it and says `software: true`, so the indicator shows;
  one started for software that finds hardware exits (a wrong start).
- **`--gpu=hardware` skips the blocklist and nothing else**: the crash policy still
  applies. `--gpu=software` starts every tab in software, or on macOS shows every tab
  the notice.
- **The crash policy lives here until 5.18.** It is a pure module with no
  dependency, its rules tested row by row and its step checked by Kani; 5.18 states
  it in the kernel's spec and proves the plan's three theorems there, with certified
  mutations.
- **Time is the host's monotonic clock in milliseconds**, given with each event; a
  time earlier than one recorded counts as no time passed.
- **A refusal is the machine's**: `GpuRefused`, or an exit before `GpuReady` in
  hardware, puts every tab in software. No page has reached a process before
  `GpuReady`, so a page cannot cause it, and these exits are not counted by site. A
  `GpuRefused` at any other time is ignored (the kernel ends that process, and its
  exit counts normally).
- **Every-tab demotion takes effect at each tab's next start**: no running process is
  ended for it, so an exit changes no other tab's state or output.
- **Only hardware exits are counted by site**, keeping the two most recent distinct
  sites; before demotion no three sites have exits in one window, so with a
  monotonic clock that is enough.
- **The window counts each tab's last two exits in its current mode**; the third
  within five minutes moves it on, and a change of mode starts the count afresh.
  "Software also fails three times" is read the same way, within five minutes.
- **A reload of a stopped tab** starts it with two exits recorded at the reload, so
  one more exit within five minutes moves it on again; a same-site navigation does
  not restart a stopped tab, another site does.
- **Exits of a replaced process are the kernel's to drop**: `Exited` is for the
  tab's current process; 5.18 gives processes ids and restates the paint theorems
  over restarts.

### Evidence

Unit tests: the blocklist (the shipped table parses and is empty; every field;
hostile text: tabs, CR, non-ASCII, NUL, DEL, every malformed field, empty ranges,
the three limits; matching at both ends of a range, wildcards, unknown versions,
software adapters, first match; pseudo-random bytes and every one-byte change of a
good line never panic and yield only well-formed entries), the start (every answer),
the crash policy (every transition, as rows: open, ready, refused, exits before and
after `GpuReady`, rules 1 to 4 with and without a fallback, sites in and out of the
window, software exits, a clock going back, navigation, reload, close, unknown tabs;
an hour of crashes giving exactly five restarts; 20,000 pseudo-random events per
platform checking containment, the invariants and the site rule at every step), and
the plan's test "a fake adapter matching a blocklist entry falls to software": a fake
device the table lists is refused before any list, the policy starts the tab in
software, and every scene drawn there equals the reference. `tests/metal.rs` now
starts through the shipped blocklist.

Kani (`src/proofs.rs`), each harness alone with the caps above:

| Harness | Covers | Result | Verification time | Wall time | Peak memory |
|---------|--------|--------|-------------------|-----------|-------------|
| `matches_any` | every entry and adapter | passed, 254 checks | 0.70 s | 5 s | < 0.01 GB |
| `note_exit_any` | one exit from any shared state meeting the invariant | passed, 255 checks | 0.72 s | 5 s | < 0.01 GB |
| `tab_step_any` | any event, any tab and shared state meeting the invariants, any time | passed, 728 checks | 1.97 s | 5 s | < 0.01 GB |
| `version_parse_any` | any input up to 8 bytes | passed, 236 checks | 30.6 s | 36 s | 1.38 GB |
| `hex_any` | any input up to 10 bytes | passed, 193 checks | 10.8 s | 15 s | 0.26 GB |
| `drivers_parse_any` | any input up to 7 bytes | passed, 384 checks | 70.7 s | 75 s | 2.77 GB |
| `policy_contained_any` | any event, two tabs in any state meeting the invariant | passed, 1,428 checks | 52.2 s | 55 s | 4.62 GB |

None reached a cap, and none was removed.

Proved for every size: the matcher (`Entry::matches`, any entry and adapter), the
site rule (`Shared::note_exit`) and one tab's step (`Tab::step`), both from any state
meeting the invariants, so for any number of tabs and any history before the step.
Bounded: `Version::parse` (inputs up to 8 bytes), `parse_hex` (10), `Drivers::parse`
(7); the policy's containment over two tabs (its step only finds the event's tab and
steps it, which `tab_step_any` covers for every state). Not proved by Kani: a whole
table's parse (covered by the tests above).

Miri, each test alone with a 10-minute cap:

| Test | Time |
|------|------|
| `blocklist::tests::limits_are_kept` | 63.5 s |
| `tests::a_listed_fake_adapter_falls_to_software` | 42.0 s (the first scene only under Miri; every scene runs there on its own) |
| `tests::bad_lists_are_refused_before_drawing` (now through `Gpu::start`) | 14.5 s |
| `policy::tests::every_step_is_contained` | 8.5 s (300 events a platform under Miri, 20,000 otherwise) |
| `blocklist::tests::arbitrary_bytes_never_panic` | 4.4 s (40 random inputs and every ninth byte under Miri, 4,000 and every byte otherwise) |
| `policy::tests::a_tab_crashing_forever_restarts_five_times` | 2.2 s |
| `blocklist::tests::hostile_text_is_refused_with_its_line` | 0.78 s |
| `blocklist::tests::the_shipped_table_parses_and_is_empty` | 0.54 s |
| the other 28 new tests | under 0.2 s each |

Times are Miri's clock (`--report-time`). The other scene tests changed only in
starting through `Gpu::start`, and were not run again under Miri here.

### Not done, and what each waits for

- **The kernel's policy and its theorems** (`theorem_gpu_exit_contained`,
  `theorem_gpu_restart_bounded`, `theorem_site_cannot_demote_others`, with certified
  mutations): item 5.18, which adds the GPU process, `GpuExited`, `GpuReady` and
  `GpuRefused` to the kernel. `src/policy.rs` is the machine to state there.
- **The software drivers**: lavapipe through the Vulkan backend, WARP through the
  Direct3D 12 backend (item 5.17b's rest). Shipping lavapipe at CI's pinned version,
  selecting it through the loader's driver-file setting, its measured size, its
  licences, and its rows in `docs/VERIFICATION.md`'s TCB and `docs/DEPENDENCIES.md`
  come with the release; nothing is shipped yet, so none is written.
- **Device descriptions**: Vulkan's `VkPhysicalDeviceProperties` (and the per-vendor
  `driverVersion` decoding) and DXGI's adapter description and driver version, with
  those backends. Metal's driver version (the OS version) would need a new audited
  `clazel-sys` call.
- **The GPU process's sandbox**: macOS and Linux are below (item 5.21a). On Linux
  a software device gets the list without `ioctl` (lavapipe's profile without
  device access); a sandbox's kill counting as a refusal is the crash policy's,
  which the host does not act on yet.
- **The host's side**: `browse --gpu=software|hardware` and the warning, the
  software indicator in the address bar strip, and the notice in the content area
  (items 5.18 and 5.23).
- **The test through real processes** (a GPU process killed mid-frame): it needs the
  GPU process's binary and the kernel's side (5.18, 5.21a, 5.26).
- **Counts across runs**: until item 3.10's store exists.

## Item 5.21a: the GPU process's sandbox

The policies are data in `clazel-sandbox` (its README has every OS, the measurement
and how this sandbox is weaker than the renderer's). What this crate adds is the
order the macOS GPU process enters it in, `sandbox::start_metal`:

1. make the Metal backend: the device, its queue and the one fixed pipeline,
   compiled from `shaders/quad.metal`;
2. enter `clazel_sandbox::seatbelt::gpu_profile()`, which is `(deny default)`
   and, since item 5.23, one `mach-lookup` of Metal's compiler service (the
   driver compiles blit variants when first needed; `clazel-sandbox`'s README has
   the measurement), through `clazel_sys::macos::sandbox_init_profile`;
3. only then `Gpu::start` (the blocklist) and the first message.

No byte from a page reaches the process before step 2. An error in either step ends
the GPU process before `GpuReady`, which the crash policy counts as a refusal.

**Measured** (Apple M1 Pro, macOS 26.7.2, 2026-11-13). `tests/sandbox_macos.rs`
is `harness = false` and runs itself again as a child for each check. It shows:
- every scene drawn after step 2 equals the unsandboxed control and the reference,
  with no denial in the system log;
- entering before step 1 leaves Metal no device;
- reading or creating a file, listing the home directory, a TCP connection, a UDP
  bind, a Unix-socket connection, reaching the WindowServer, `fork` and starting a
  program are each allowed unsandboxed and denied inside.

It opens no window and takes no focus. It waits for every child, with a two-minute
limit, and leaves nothing running. A missing Metal device is a skip, except under
CI; under Miri it does nothing.

**Not measured:**
- other Macs and macOS versions;
- a long-running or memory-starved GPU process;
- the Mach port that will bring the host's surfaces (item 5.18).

### Linux (`sandbox::start_vulkan`)

The order is in `src/sandbox.rs`: `no_new_privs` and the namespaces (user, mount,
network, IPC; no PID namespace, after which the kernel refuses new threads) while
there is one thread; the Vulkan backend; a warm-up frame of our own, drawn, read
back and checked; Landlock with no rule; then the seccomp list on every thread at
once. The list (`clazel-sandbox`'s `syscalls::GPU_EXTRA`) was measured on lavapipe
on aarch64 Linux and narrowed to what was called; with a hardware device `ioctl`
is added, which **no hardware driver has been measured with**. x86-64 has not been
measured either.

Windows has no GPU backend yet, so nothing in this crate enters its policy.

## The Vulkan backend

`src/vulkan.rs`, over `clazel_sys::linux::vulkan` (46 Vulkan functions, every one
in Vulkan 1.0, and `memcpy`; the audit of that change is outstanding). It draws
offscreen into an `R8G8B8A8_UNORM` image with the committed SPIR-V and reads the
target back; the file's head lists its choices (one submission for each run of
draws, each waited for; storage buffers for the quads and the atlas; which device
is chosen). The instance asks for Vulkan 1.1 and older devices are refused,
because the SPIR-V uses the `StorageBuffer` storage class.

**Where it has run**: only on lavapipe (Mesa 25.2.8, LLVM 20.1.2) in an aarch64
Ubuntu 24.04 container on an Apple silicon Mac.

- `tests/vulkan.rs`: every scene is within one level of the software reference
  (the two mask scenes differ by one level in 128 and 192 channels, the rest by
  nothing), and equals the pixels stored for aarch64 (`tests/pixels-lavapipe-aarch64`).
- The Khronos validation layer (1.3.275) reports nothing over those tests. It
  did report the SPIR-V's storage class against a 1.0 instance, which is why the
  instance asks for 1.1.
- `clazel`'s `tests/browse_gpu.rs` (16 tests: hand-built lists, real pages,
  resizes, scrolls, a navigation, `browse --headless`) passes with the GPU
  process in its sandbox.

**Not run**: x86-64 (CI's architecture; no pixels are stored for it, so CI
compares with the reference only), any hardware driver, another Mesa version.

## Item 5.23: the GPU process

`src/main.rs` is the `clazel-gpu` binary, which the host starts when the kernel says
`SpawnGpu` (`clazel_renderer::launch::Gpus`); `src/process.rs` is its loop, over any
backend; `src/channel.rs` frames its two sockets besides the kernel's.

1. Standard input and output are the kernel's channel, as a renderer's.
2. `--list-fd N` and `--surface-fd M` are the list socket (from the paired renderer)
   and the surface socket (to the host), inherited by number: the host clears their
   close-on-exec flags for this one start (`clazel_sys::macos::clear_close_on_exec`).
   They are opened again through `/dev/fd`, with no `unsafe`, **before** the sandbox.
3. Then 5.21a's order: Metal, the sandbox, the blocklist, `GpuReady` or `GpuRefused`.
4. The loop: `GpuViewport` sets the size; every list is drawn, in order (before a
   viewport, on a 1 by 1 target with no frame sent, so the masks stay the
   renderer's); each drawn list's pixels go on the surface socket in the next ring
   slot (0, 1, 2, 0, …), then `FrameReady { buffer: slot, width, height }` to the
   kernel. A `GpuViewport` alone draws nothing: the renderer sends a new list.
5. It ends on any error or when either input closes, and says why on stderr.

### How buffers pass on macOS (a decision, until the Mach-port route)

The plan moves an IOSurface to the host with a Mach port (5.21, 5.21a), which needs
new `clazel-sys` calls and a prototype nobody has built, and on Linux names a
`memfd`, which macOS lacks. Until then, **the ring is the host's**: three slots per
GPU process, each a copy of a frame's RGBA8 pixels that the GPU process sends on the
surface socket (12 bytes of slot, width and height, then the pixels; slots and sides
checked before anything is allocated, so at most 256 MiB a frame) and then names in
`FrameReady`. The kernel still decides which slot is shown under which URL; the host
shows only a slot a `Paint` names, and only pixels of the `Paint`'s size. The cost is
a copy of each frame through a socket and into the host's memory (and the host
composites it over white into a `CGImage`), which the plan's route avoids; the host
reads the bytes as pixels and nothing else. A compromised GPU process can show its
own tab stale or wrong pixels, which its renderer could already draw, and can make
the host allocate up to 256 MiB a frame.

### Evidence

- `channel.rs`: lists and frames round-trip, a cut or oversized list is an error, a
  frame header naming slot 3, a side of 0 or 2^31 is refused before allocating.
- `process.rs`: a list before a viewport sends nothing and the ring turns 0, 1, 2, 0;
  anything but `GpuViewport` from the kernel, a viewport over 8192 and a list that
  does not decode end the process; and the whole loop on sockets with the fake
  backend draws every scene's lists equal to the reference, each followed by its
  `FrameReady`.
- Through real processes (`crates/clazel/tests/browse_gpu.rs` and
  `browse_window.rs`, macOS): the real `clazel-gpu`, sandboxed on Metal, draws a
  hand-built list sent by a stand-in renderer; the kernel's `Paint` names slot 0
  under the kernel's URL; its pixels equal the reference within one level; the
  window shows them; `browse --headless` writes them as a PNG and a PPM.
- With the real renderer (5.20, same tests): a styled page is painted at its
  viewport, painted again for a new viewport and for scrolls down and back, and a
  click on its link navigates and paints the next page; `browse --headless` writes a
  real page's PNG (its size, its background, its text's ink); and, opt-in because it
  takes focus, `clazel browse URL` shows a real page in its window.
- The renderer's list framing and this reader are one definition (`channel.rs`), and
  `clazel-renderer`'s `the_gpu_process_reads_what_the_renderer_writes` runs its
  bytes through `process::Server`.

### Not done

- The Mach-port route (no copy), and Linux's `memfd`.
- `--software`: macOS has no software Metal driver (5.17c), so the process is only
  started for hardware.
- The kernel does not yet act on `GpuReady`, `GpuRefused` or the process's exit
  (5.17c's crash policy in the kernel), so the host only logs an exit.

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
