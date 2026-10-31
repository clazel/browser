# Roadmap

**Long-term goal:** a general-purpose web browser whose security-critical
core is formally verified and whose entire codebase is memory safe. It will be
written by AI, and checked by machines.

**Platforms:** macOS and Linux first. Windows is partly done early: the
workspace builds and its tests pass on Windows, and the renderer runs in an
AppContainer (a less-privileged one, with a Job Object and process
mitigations; policy in `clazel-sandbox`'s `appcontainer`, calls in
`clazel-sys`'s `windows`, started by `clazel-renderer`'s `launch`). The rest of
phase 8 stays: the proofs (Verus, Kani) and `scripts/verify.sh` are not run
on Windows, there is no Windows CI job, and the `clazel-sys` change is not
audited yet (`docs/SYS-AUDITS.md`).

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
taken: option B. Everything but TLS is on `main` (HTTP, DNS, the fetch
client with redirects and cookies, the kernel join, and the `http://` half
of the `curl` clone); TLS (3.5) is on open pull requests.**

## Phase 4: HTML and DOM
WHATWG tokenizer (proven total and panic-free), tree builder, DOM.
*Exit:* a text-mode browser (Lynx-style) that browses real sites.
Detailed plan: [phases/phase-4.md](phases/phase-4.md).
**Status: built (2026-10-31), not complete.** Every item but 4.4 is merged
into `main` (the last at `9f776b2`): `clazel-html` (tokenizer, character
references, encoding sniffing) and `clazel-treebuilder` are at tier 2, the
kernel's display theorems are proven, and `clazel browse` runs on `http://`
sites. CI's full verification at `e29265d`
([run 41140621041](https://github.com/clazel/browser/actions/runs/41140621041)) had every job
green but Miri, which overran its 360-minute limit (traced to the Phase 3
TLS tests; fix open as PR #75). Left: a green full run, and `clazel-dom` at
tier 2 (`phase4/dom-conformance-tier2`). Item 4.4 (multi-byte encodings)
moved to Phase 8.
<!-- Once both hold, replace the paragraph above with this line, filling in the date, sha and run id: -->
<!-- **Status: complete (YYYY-MM-DD).** CI's full verification passed at `<sha>` ([run <id>](https://github.com/clazel/browser/actions/runs/<id>)). -->

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
Windows CI and proofs (the AppContainer backend exists, see Platforms). WPT score tracking, CSS breadth,
Web APIs, performance. Also the legacy multi-byte encodings (gb18030 and
GBK, Big5, ISO-2022-JP, Shift_JIS, EUC-JP, EUC-KR), slipped from Phase 4
item 4.4 as its item 4.0 allows; until then a page in one of them is not
rendered and says "encoding `<name>` is not supported"
([phases/phase-4.md](phases/phase-4.md#44-legacy-multi-byte-encodings-l-may-slip-to-phase-8-per-40)).
