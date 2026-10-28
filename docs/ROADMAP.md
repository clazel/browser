# Roadmap

**Long-term goal:** a general-purpose web browser whose security-critical
core is formally verified and whose entire codebase is memory safe. It will be
written by AI, and checked by machines.

**Platforms:** macOS and Linux first. Windows comes later (phase 8).

**Non-goals for now:** JIT compilation, extensions, DRM, WebGL/WebGPU.

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
*Exit:* a verified `curl` clone.
Detailed plan: [phases/phase-3.md](phases/phase-3.md).
**Status: in progress (started 2026-10-23). The TLS decision (3.0) is
taken: option B.**

## Phase 4: HTML and DOM
WHATWG tokenizer (proven total and panic-free), tree builder, DOM.
*Exit:* a text-mode browser (Lynx-style) that browses real sites.
Detailed plan: [phases/phase-4.md](phases/phase-4.md).
**Status: planned (2026-10-28).** The decisions in item 4.0 are taken
(tree builder and DOM at tier 2, single-byte legacy encodings in the phase,
the body chunked to the renderer); nothing is built.

## Phase 5: CSS, layout, graphics (the Show HN milestone)
CSS parsing and cascade, block, inline and table layout, font parsing and
shaping, raster, and a native window on macOS and Linux.
*Exit:* **renders news.ycombinator.com correctly**, so the Show HN post can be
read in the browser it announces.

## Phase 6: Images and forms
PNG, JPEG, GIF and WebP decoders (Tier 1, written in the style of WUFFS), plus
form submission.

## Phase 7: JavaScript
Interpreter only, no JIT. The GC uses an index-based arena so the heap stays
in safe Rust. DOM bindings.
*Exit:* common sites work, more slowly than in a JIT-based browser.

## Phase 8: Windows port, compatibility grind
Windows sandbox backend (AppContainer). WPT score tracking, CSS breadth,
Web APIs, performance.
