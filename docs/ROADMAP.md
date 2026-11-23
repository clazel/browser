# Roadmap

**Long-term goal:** a general-purpose web browser whose security-critical
core is formally verified and whose entire codebase is memory safe. It will be
written by AI, and checked by machines.

**Platforms:** macOS and Linux first. Windows is partly done early: the
workspace builds and its tests pass on Windows, and the renderer runs in an
AppContainer (a less-privileged one, with a Job Object and process
mitigations; policy in `clazel-sandbox`'s `appcontainer`, calls in
`clazel-sys`'s `windows`, started by `clazel-renderer`'s `launch`), CI has a base
Windows job, and Phase 5 adds the window and GPU drawing on Windows. The rest of
phase 8 stays: the proofs (Verus, Kani) and `scripts/verify.sh` are not run on
Windows.

**Non-goals for now:** extensions, DRM, WebGL/WebGPU. (JIT compilation was a
non-goal until 2026-11-16; it is now part of Phase 7.)

Each phase ends in something you can run.

## Phase 0: Foundations
Workspace, lints, a local verification gate that rejects unproven code in Tier 2 crates,
contributor rules for AI agents (`CLAUDE.md`), and honesty metrics script.
*Exit:* see the detailed plan in [phases/phase-0.md](phases/phase-0.md).
**Status: complete (2026-10-19).**

## Phase 1: Verified primitives
UTF-8 encoding, percent-encoding, base64, MIME sniffing, WHATWG URL parser.
*Exit:* WPT `url/` tests pass and the parsers are proven against spec functions.
Detailed plan: [phases/phase-1.md](phases/phase-1.md).
**Status: complete (2026-10-21).** `scripts/verify.sh` passes on macOS arm64,
and CI's full verification passed on Linux x86-64 at `619d7dd`
([run 39652504757](https://github.com/clazel/browser/actions/runs/39652504757)).

## Phase 2: Kernel and IPC
Quark-style process model. A small kernel process owns all network, cookie
and storage access. Each tab is a sandboxed renderer process that can only
send typed messages. Same-origin policy is a proven property of the kernel.
*Exit:* two renderer processes that provably cannot read each other's cookies.
Detailed plan: [phases/phase-2.md](phases/phase-2.md).
**Status: complete (2026-10-28).** Every item is built and the theorems are
proven at tier 2. CI's full verification passed at `872c1e8`
([run 40642618793](https://github.com/clazel/browser/actions/runs/40642618793)),
running the demo and the escape tests on Linux x86-64 and macOS arm64.

## Phase 3: Networking
Verified HTTP/1.1 parser, DNS, and our own TLS 1.3 client with verified
crypto from libcrux (decided in phase-3.md item 3.0; rustls was not taken).
A generic proven store on the WHATWG Storage model that keeps the cookie jar,
`localStorage` and the history across runs (3.10), added 2026-11-03. Later
phases add IndexedDB, the Cache API and an HTTP cache to the same store.
*Exit:* a verified `curl` clone.
Detailed plan: [phases/phase-3.md](phases/phase-3.md).
**Status: in progress (started 2026-10-23). The TLS decision (3.0) is
taken: option B. HTTP, DNS, the fetch client with redirects and cookies, the
kernel join, the TLS client and the `curl` clone over `http:` and `https:` are
on `main` (CI's full verification green on bf6a9ea). Since then `clazel-tls`
and `clazel-p384` are at tier 2 and the store (3.10a, `clazel-store`) is at
tier 2. Left: `clazel-x509` at tier 2 (it is at tier 0), the store's first
consumers (3.10b), so cookies and history still do not outlive a run, and
the wrap-up (3.9).**

## Phase 4: HTML and DOM
WHATWG tokenizer (proven total and panic-free), tree builder, DOM.
*Exit:* a text-mode browser (Lynx-style) that browses real sites.
Detailed plan: [phases/phase-4.md](phases/phase-4.md).
**Status: complete (2026-11-15).** CI's full verification passed at `72e11de` ([run 43742499291](https://github.com/clazel/browser/actions/runs/43742499291)).
`clazel-html`, `clazel-treebuilder` and `clazel-dom` are at tier 2. Item 4.4
(multi-byte encodings) moved to Phase 8.

## Phase 5: CSS, layout, graphics (the Show HN milestone)
CSS parsing and cascade, block, inline and table layout, font parsing and
shaping, GPU raster, and a native window on macOS, Linux and Windows.
*Exit:* **renders news.ycombinator.com correctly**, so the Show HN post can be
read in the browser it announces.
Detailed plan: [phases/phase-5.md](phases/phase-5.md).
**Status: built, not complete.** On `main` (CI's full verification green at
`72e11de`, [run 43742499291](https://github.com/clazel/browser/actions/runs/43742499291)):
`clazel URL` opens a window on macOS, Linux and Windows and draws the page
through a sandboxed renderer and a sandboxed GPU process per tab (Metal,
Vulkan, Direct3D 12), with linked style sheets fetched by the kernel, the
cascade, block, inline and table layout, system fonts, and an address bar
that is the kernel's; `--headless` writes a PNG. Left: the tier raises, each
waiting on its evidence: `clazel-css`, `clazel-selectors` and
`clazel-displaylist` to tier 2, `clazel-style`, `clazel-font` and
`clazel-glyph-mask` to tier 1 (each is at tier 0); deleting `clazel-text`
(5.0(g)); and phase-5.md's Status table, which still reads as before the
work began.

## Phase 6: Images and forms
PNG, JPEG, GIF and WebP decoders (Tier 1, written in the style of WUFFS), plus
form submission.
*Exit (6.0(g)):* news.ycombinator.com with its images, and logging
in, voting and commenting through its own forms.
Detailed plan: [phases/phase-6.md](phases/phase-6.md).
**Status: planned (2026-11-16); decisions in item 6.0 taken the same day.**

## Phase 7: JavaScript
A baseline JIT is the main path, on Windows x86-64, Linux x86-64 and macOS
arm64 from the start (decided 2026-11-16). A thin interpreter loop over the
same op handlers runs cold code, serves as the JIT-off mode and is the
reference for testing. Every code blob passes a tier 2 validator for its
instruction set before it can run, which proves the code stays in its
memory regions and jumps only inside itself. Each op's code is proven to
refine the bytecode semantics, a Verus spec. The GC uses an index-based
arena so the heap stays in safe Rust. DOM bindings. The machine-code half
(instruction-set specs, IR, back ends, validators) is built so that a later
WebAssembly front end reuses it.
Detailed plan: [phases/phase-7.md](phases/phase-7.md); the JIT in
[phases/jit.md](phases/jit.md).
**Status: planned (2026-11-16); decisions in items 7.0 and J.0 taken; no
item started.**
*Exit:* common sites work; Test262 gives the same results with the JIT on
and off on all three platforms.

## Phase 8: Windows port, compatibility grind
Windows proofs (the AppContainer backend, base CI job and Phase 5's window exist, see Platforms). WPT score tracking, CSS breadth,
Web APIs, performance. Also certificate revocation through a pushed set
([phases/phase-3.md](phases/phase-3.md), item 3.5h, moved here on 2026-11-05):
until then a revoked certificate that has not expired is accepted. Also the legacy multi-byte encodings (gb18030 and
GBK, Big5, ISO-2022-JP, Shift_JIS, EUC-JP, EUC-KR), slipped from Phase 4
item 4.4 as its item 4.0 allows; until then a page in one of them is not
rendered and says "encoding `<name>` is not supported"
([phases/phase-4.md](phases/phase-4.md#44-legacy-multi-byte-encodings-l-may-slip-to-phase-8-per-40)).
