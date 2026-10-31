# Phase 5: CSS, layout, graphics (the Show HN milestone), detailed plan

**Goal:** the renderer draws the page instead of describing it. The style
sheets a document names are parsed inside the sandbox (CSS Syntax Level 3),
their selectors are matched against the DOM arena Phase 4 built (Selectors
Level 4), the cascade gives every element its computed style (CSS Cascade
Level 4, with HTML §15's user agent style sheet and presentational hints), the
boxes are laid out as blocks, lines and tables (CSS 2.1 §9, §10, §17, CSS Text
Level 3), the text is set in fonts read from OpenType files, and a rasterizer
of our own turns the result into pixels. The host gains a native window on
macOS and Linux, with an address bar the renderer cannot draw on. The kernel
keeps its two display theorems in a new shape: a renderer's pixels are shown
only in its own tab, under the URL the kernel committed there, and never
outside the viewport the host gave it.

*Exit:* `cargo run -p clazel -- browse https://news.ycombinator.com/` opens a
window that shows the Hacker News front page laid out as a reference browser
lays it out, and the Show HN post's item page with its comment tree can be
read in it, with every parser on that path at its target tier.

Nothing in this phase decodes an image, submits a form or runs a script.
Images are Phase 6: an `img` is a box of the size its attributes give, drawn
empty, which is what Hacker News' spacer images need for the comment tree's
indentation. Forms are Phase 6: an `input` or a `textarea` is an empty
bordered box. JavaScript is Phase 7: `hn.js` is never fetched, so comments
cannot be collapsed and votes cannot be cast. Floats, positioning, flexbox,
grid, transforms, `@font-face`, bidirectional text and complex-script shaping
are not needed by the exit page (see "What the exit page needs") and are Phase
8's CSS breadth unless 5.0(b) widens the subset.

A convention for this file: a section number marked † was written from the
documents as remembered, not read at a pinned commit, and must be checked
against the commit a spec header pins before it is cited there (SPEC-STYLE.md,
"Pin the source"). Numbers without the mark are either already cited in this
repository (HTML §15.3.1 to §15.3.3, §15.3.6 to §15.3.8, §15.3.10 and
§15.3.11, in `clazel-text` and phase-4.md; Encoding §6) or are CSS 2.1's (the
Recommendation of 7 June 2011, whose numbering is fixed); they too are checked
at the pinned text before a spec header cites them.

## Exit criteria

Phase 5 is done when all of these hold on macOS arm64 and Linux x86-64:

1. **Tiers**, as 5.0 decides them and `cargo xtask check` accepts. As
   recommended: `clazel-css` and `clazel-selectors` at **tier 2** (every
   mutation a certified `killed`, conformance tests, an independent
   transcription each); `clazel-style`, `clazel-font` and `clazel-raster` at
   **tier 1** (Kani harnesses over all inputs up to stated bounds);
   `clazel-layout`, `clazel-window`, `clazel-renderer` and `clazel` at tier 0
   with their items' evidence; `clazel-ipc` and `clazel-kernel` still at tier
   2 with 5.18's and 5.19's schema and theorems.
2. **Suites**, vendored at pinned commits, run through the shipped code, each
   printing its `clazel-conformance:` line (`xtask/src/conformance.rs`) with
   every expected failure listed by name and reason: CSS syntax, Servo's
   `css-parsing-tests` and WPT `css/css-syntax/` cases, plus a `cssparser`
   differential (5.4); selectors, WPT `css/selectors/` parsing cases and
   reftests, plus a differential against Servo's `selectors` (5.5); style, WPT
   `css/css-cascade/` reftests and the `css-color`, `css-values` and
   `css-fonts` parsing cases for the subset (5.6, 5.7); fonts, differentials
   against `ttf-parser` and `read-fonts` on vendored, system and mutated fonts
   (5.9, 5.10) and kerning against `rustybuzz` (5.11); line breaking,
   Unicode's `LineBreakTest.txt` (5.12); layout and paint, a stated list of
   WPT `css/CSS2/`, `css/css-tables/`, `css/css-text/white-space/` and
   `quirks/` reftests, both pages of each rendered by our engine and compared
   pixel for pixel, with WPT's `fuzzy` annotations honoured and nothing else
   tolerated (5.25).
3. **Demo.** `cargo run -p clazel -- browse URL` opens a window with an
   address bar the host draws, the page below it, scrolling by wheel and keys,
   and links followed by a click. On `https://news.ycombinator.com/` and a
   Show HN item page, run locally (no Internet in CI), every story's rank,
   title, site, score, user, age and comment count, and every comment with its
   indentation, are readable; the text runs' boxes are within 5.25's stated
   tolerance of a recorded reference engine's, and the pixel difference from
   its screenshot is measured and reported, not asserted. In CI the same
   checks run on 5.26's HN-shaped fixture from an in-process server, against
   our own stored screenshot, compared exactly. Until Phase 3's TLS is in the
   kernel (5.0(f)), the demo runs on `http://` sites and the fixture, and this
   criterion says so.
4. **Kernel theorems** (5.18, 5.19): `theorem_paint_only_own_tab`,
   `theorem_address_bar_integrity` (the URL shown with a renderer's pixels is
   the kernel's committed URL for its tab, whatever the renderer sends),
   `theorem_paint_fits_viewport`, `theorem_paint_is_the_surface`,
   `theorem_input_only_to_own_tab`, `theorem_subfetch_only_to_requester` and
   `theorem_subfetch_credentials`; the Phase 2 to 4 theorems restated over the
   new events and outputs.
5. **Hostile pages** (5.26: a CSS bomb, a font with malicious tables, a
   million-element page, a page that tries to draw over the address bar, and
   the rest) never panic a renderer, exceed its stated memory bound or time,
   or change what the host draws outside the content area.
6. **Miri:** every new `tests/conformance*.rs` runs a stated stride under Miri
   (`if cfg!(miri) { N } else { 1 }`, with the reason), sized to about a
   minute; no test takes 300 s of Miri's time or more; the Miri job finishes
   inside its CI limit.
7. `scripts/verify.sh` exits 0 and CI's full verification is green on the pull
   request that completes the phase; VERIFICATION.md's TCB names the window
   bindings, the compositor and the system font files; every `clazel-sys`
   change has an audit row by another session (rule 1).

## What is proven, and what is assumed

1. **Proven (Verus, tier 2, as 5.0(a) recommends):** the CSS Syntax 3
   tokenizer and parser as total functions, whole-input and one-step faces
   proven equal; Selectors 4 parsing, matching against the DOM arena and
   specificity; the codec over the new messages (`clazel-ipc`); and the
   kernel's paint, input and style sheet fetch theorems (5.18, 5.19).
2. **Proven free of panics and overflow (Kani, tier 1):** the property value
   parsers, the cascade and computed values (`clazel-style`); the OpenType
   table parsers and outline decoding (`clazel-font`); the rasterizer
   (`clazel-raster`). Each harness covers every input up to a bound written in
   the harness and the crate's README; correctness evidence is the conformance
   and differential tests.
3. **Small and tested (Tier 0, listed in VERIFICATION.md's TCB):** the layout
   (`clazel-layout`), the renderer's pipeline glue, and the host's window code
   (`clazel-window`) and event loop. Layout and glue run in the sandbox, so a
   bug there can mis-render or kill one tab but not break a kernel theorem;
   their evidence is the reftests, the reference harness and the hostile
   pages.
4. **Assumed (TCB), new:** the OS windowing system and compositor (AppKit and
   the WindowServer; the X server, or XWayland and a Wayland compositor); the
   windowing bindings 5.0(e) chooses; GPU drivers only if 5.0(d) brings a GPU
   in; the system font files read by path (5.0(c)); and, as evidence that the
   specs match the standards, the suites and engines of the differential
   tests.

What a bug can and cannot do: style, fonts, layout and raster all run in the
renderer, inside the sandbox, on bytes a server chose. A bug there can draw
wrong pixels for its own tab or kill it. It cannot draw outside its tab's
content area or change the address bar, because the kernel checks the size of
what it shows (`theorem_paint_fits_viewport`), labels it itself
(`theorem_address_bar_integrity`), and the host draws the address bar in a
strip no surface is placed in (5.23, tested in 5.26). The host's window code
is outside the sandbox and is the one new place where a bug matters to every
tab; the only page-derived bytes it reads are pixels whose size the kernel has
checked.

Not covered by any theorem, and said so: that the page looks right (the
reftests and the reference harness are the evidence); timing and memory beyond
the stated bounds; `:visited`, which never matches, and `:hover`, which has no
state yet (5.5); characters no font maps (drawn as `.notdef`); right-to-left
text (drawn in logical order); and the host's composition of chrome and
content, which is Tier 0 code with a test, not a theorem.

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-css` | 0 (2, per 5.0(a)) | CSS Syntax 3 §3 to §6, §9 (all †); CSSOM "serialize" for tests | input decoding for style sheets, the tokenizer, the parser's entry points and algorithms, component values, An+B, serialization of tokens |
| `clazel-selectors` | 0 (2, per 5.0(a)) | Selectors 4 §3 to §7, §9, §15 to §17, grammar, API hooks (all †) | parse a selector list, match against `clazel-dom`'s arena, specificity, serialization |
| `clazel-style` | 0 (1) | CSS Cascade 4 §4, §6, §7; CSS 2.1 §6; CSS Values 4; CSS Color 4; CSS Fonts 3 §3; Media Queries 4 (subset); CSS Style Attributes; HTML §15.2 to §15.5; Quirks Mode | property value grammars of the subset, shorthands, the user agent style sheet, presentational hints, the cascade, inheritance, computed values as a side table keyed by node id |
| `clazel-font` | 0 (1) | OpenType 1.9† (font file, collections, `cmap`, `head`, `hhea`, `hmtx`, `maxp`, `loca`, `glyf`, `name`, `OS/2`, `post`, `kern`, `GPOS` type 2; `CFF` per 5.0(c)); Apple TrueType Reference Manual (second text) | the table directory, each table's parser, glyph outlines as quadratic contours, advances, kerning lookups |
| `clazel-layout` | 0 (0) | CSS 2.1 §8 to §11, §16, §17, Appendix E; CSS Text 3; CSS Tables 3 (auto layout)†; UAX #14; HTML §15.3, §15.4; Quirks Mode §3 | the box tree, block, inline and table formatting, white space, line breaking, font matching and the shaping glue, hit testing, the display list. **Replaces `clazel-text`** (5.0(g)) |
| `clazel-raster` | 0 (1, per 5.0(d)) | none (ours); the OpenType `glyf` chapter fixes the outline semantics | paths (lines, quadratic Béziers), flattening, anti-aliased coverage, fills, glyph masks, clipping, blending into an RGBA surface |
| `clazel-window` | 0 (0) | X Window System Protocol (X11R7)† on Linux; Apple's AppKit and Core Graphics documentation on macOS | the host's window: open, present a surface, read events; per 5.0(e) |
| `clazel-ipc` | 2 (exists) | RFC 8949 §3; ours | the messages of 5.18 and 5.19 |
| `clazel-kernel` | 2 (exists) | ours; Fetch for 5.19's request | viewports, paint routing, input routing, style sheet fetches, the theorems |
| `clazel-renderer` | 0 (exists) | — | the pipeline of 5.20, inside the sandbox |
| `clazel-sys` | 0 (exists) | man pages and Apple documentation | per 5.0(e): the macOS window calls, audited |
| `clazel` | 0 (exists) | — | `browse` with a window; the host shell stays under 300 lines |

Each new Tier 1 or Tier 2 crate starts as `tier = 0` with its target, as in
Phases 1 to 4. Syntax, selectors and style are three crates because a tier is
a property of a crate: the syntax crate's tier 2 must not wait for the
cascade, and the style crate's tier 1 must not be held to tier 2 by a crate
boundary. Font parsing and rasterization are separate because the rasterizer
also fills the boxes layout makes, and its harnesses are about arithmetic, not
bytes.

Section numbers are from the documents at the time of writing; each spec
header pins the exact commit or dated version it transcribes.

## Dependencies on Phases 3 and 4

**Phase 4** gives the input and the display channel. Used as they are:
`clazel-dom`'s arena (its readers, and the document's quirks mode, which the
tree builder sets in the "initial" insertion mode); `clazel-treebuilder`'s
`exec::driver::parse_real`; steps 1 to 4 of the renderer pipeline (content
type, sniffing, decoding, base URL: `crates/clazel-renderer/src/pipeline.rs`'s
module comment); `clazel-encoding`'s proven Encoding §6 "decode", which CSS
Syntax's input step calls; and the commit protocol (`Commit`, `Body`,
`BodyEnd`). Replaced: the text layout (`clazel-text`, step 5), the `Display`
message (tag 10, `crates/clazel-ipc/src/message/spec.rs`), the kernel's `Show`
output (`crates/clazel-kernel/src/spec.rs`) and `browse`'s printing loop
(`crates/clazel/cli/browse.rs`). Phase 4's "Looking ahead" fixed the shapes
used here: selector matching reads the DOM through its readers; computed style
and the layout tree are side tables keyed by node id; `<style>` text and
`style` attributes are kept; a renderer's `Navigate` is how a click navigates.

**Phase 3** gives the network. The exit site is `https://` only
(`http://news.ycombinator.com/` answers `301` to
`https://news.ycombinator.com/`, measured 2026-10-31), and TLS is not in the
kernel's fetch: 3.5b's path validation, 3.5e's production providers, 3.5f's
libcrux and X.509 joins and 3.5g are open, and the host fails every `Connect`
with `tls` (phase-3.md, Status, rows 3.5b to 3.5g and 3.7). That work is a
**prerequisite of the exit and Phase 3's, not this phase's** (5.0(f)); every
Phase 5 item is built and tested against `http://` sites and the in-process
server, and only the last step of the demo waits.

## What the exit page needs

Measured on 2026-10-31 by fetching `https://news.ycombinator.com/` (34,653
bytes), its style sheet `news.css` (7,456 bytes) and one item page with 115
comments (164,969 bytes), and counting tags, attributes, inline styles,
selectors and properties; 5.1 repeats this with a script.

- **No `<!DOCTYPE>`:** both pages start `<html lang="en" op="news">`, so the
  document is in **quirks mode**: the Quirks Mode Standard's CSS quirks apply,
  and so does HTML §15.3.8's quirks-mode rule that tables do not inherit
  `font-size` and related properties (which is why `news.css` repeats its
  `body` rule for `td`).
- **Markup:** tables nested four deep for the whole layout (`<table
  id="hnmain" width="85%" bgcolor="#f6f6ef">`), `center` (33 on the front
  page, 119 on the item page), `span`, `a`, `div`, `p`, `br`, `b`, `i`, `u`,
  `pre` and `code`, `font size="1"` (116), a `form` with `input` and
  `textarea`, and `img`: the 18×18 logo and spacers `<img src="s.gif"
  height="1" width="40">` whose `width` (0, 40, 80, …) is the comment tree's
  indentation.
- **Presentational attributes:** `width`, `height`, `bgcolor`, `border`,
  `cellpadding`, `cellspacing`, `align`, `valign` (117 on the item page),
  `colspan`, and `size` and `color` on `font`.
- **Style:** one external sheet, `<link rel="stylesheet" type="text/css"
  href="news.css?…">`, same-origin (so a style sheet fetch, 5.19); inline
  `style` attributes (`height:5px` on 30 rows, `margin-top:2px;
  margin-bottom:-10px;` on 115 comment wrappers, `padding`, `text-align`,
  `line-height`, `display:block`, `border:1px white solid`); no `<style>`.
- **Selectors in `news.css`:** type, class, ID, descendant, compound
  (`span.pagetop`), attribute (`input[type='submit']`, `input[readonly]`,
  `img[src='s.gif'][width='40']`), `:link`, `:visited`, `:hover`, lists. No
  child, sibling or structural pseudo-classes.
- **Properties:** `font-family` (`Verdana, Geneva, sans-serif`, `monospace`),
  `font-size` (`pt`, `px`, `inherit`), `color` (hex), `background`,
  `background-color`, `text-decoration`, `margin` and `padding` with longhands
  (negative margins included), `border`, `width`, `min-width`, `max-width`,
  `height`, `line-height`, `text-align`, `vertical-align`, `display` (`none`,
  `block`, `inline-block`), `visibility`, `overflow`, `white-space`
  (`pre-wrap`, `nowrap`), `overflow-wrap: anywhere`, `word-break: break-word`,
  `text-overflow`, `resize`, `cursor`, `pointer-events`, `transform`,
  `page-break-before`, background images with `url()` and `linear-gradient()`,
  `!important`, and vendor-prefixed properties.
- **At-rules:** eleven `@media only screen and (min-width: …) and (max-width:
  …)` rules (comment widths by viewport) and one on
  `-webkit-min-device-pixel-ratio` and `min-device-pixel-ratio`. No `@import`,
  `@font-face` or `@supports`.

So the exit needs, beyond blocks and lines: the auto table layout, quirks
mode, presentational hints, media queries on width, negative margins and
margin collapsing, `overflow: hidden` clipping, replaced boxes sized by
attributes, and one sub-resource fetch. It does not need floats, positioning,
flexbox, grid, images or `@font-face`; the vote arrow's `transform` can be
ignored. Properties parsed but not applied are listed in 5.6, so a later phase
adds only their effect.

## Looking ahead: what Phases 6 to 8 will do with this

- **Images and forms (Phase 6)** paint into the replaced boxes 5.13 sizes from
  attributes, through the display list's image item (5.16), and take keys
  through 5.18's `Input`. Their fetches reuse 5.19's request shape.
- **JavaScript (Phase 7)** reads `clazel-style`'s side table for
  `getComputedStyle` and asks for restyle and relayout; this phase recomputes
  the whole document, keyed by node id so an incremental driver can come
  later. CSSOM needs the serializations 5.4 and 5.5 build.
- **Web fonts** make font files page-controlled bytes; `clazel-font` is
  written for that now (Tier 1, hostile fonts in 5.26) and loads only local
  fonts.
- **Nested browsing contexts** are designed in 5.24 and built later.
- **CSS breadth (Phase 8):** floats, positioning, flexbox, grid, transforms,
  bidi, complex shaping, `@import`, `@supports`.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or more.
Each item follows CLAUDE.md rule 3 where its crate has a Tier 2 target: spec
and contracts in one commit, then the implementation and proof. Items in Tier
1 crates commit the Kani harnesses' statements first. The decisions of 5.0 are
pending; the items are written for the recommendations and say where another
choice changes them.

### 5.0 Decisions for the maintainer (S) — to decide

Nine choices the maintainer makes before the items that depend on them. None
is taken here; each has options, grounds, costs and a recommendation.

**(a) The CSS parser's tier.** VERIFICATION.md requires at least Tier 1 for
"every other parser of untrusted bytes: CSS, image decoders, font tables";
every parser built so far (URL, HTTP, DNS, HTML, the tree builder) went to
tier 2. **A:** tier 2 for `clazel-css`, `clazel-selectors` and `clazel-style`;
cost: the property grammars and computed-value rules are many small
specifications, each with a spec, proof, second transcription and certified
mutations, several L items more. **B:** tier 1 for all three, the policy's
minimum; cost: the Show HN claim that every parser on the path carries
machine-checked proofs holds for CSS only in the weaker sense. **C:** tier 2
for syntax and selectors, tier 1 for style. The tokenizer and parser are a
state machine with numbered steps, the shape tier 2 has handled five times;
selectors are a small grammar and a match over a DOM already proven well
formed; property grammars are wide and shallow, which suits Kani.
**Recommendation: C**, with the demo not waiting on the proofs (as 4.0(a)):
every style sheet byte passes first through tier 2 code, and tier 1 covers the
per-property reading of parsed component values. VERIFICATION.md's "Tier 2
required" gains "CSS syntax and selectors" if C or A is taken.

**(b) The CSS subset.** **A: what the exit page needs**, measured ("What the
exit page needs"; 5.1 re-measures with a script, and anything new joins the
subset or the "parsed, no effect" list). **B: a CSS 2.1-shaped subset**: A
plus floats (§9.5), relative, absolute and fixed positioning (§9.3, §9.6,
§10.3.7†, §10.6.4†), `z-index` (Appendix E in full), generated content (§12),
`clear`, the collapsing border model and `outline`; cost: floats and
positioning are each an L item that interacts with every other layout rule,
though more of WPT's `CSS2/` would pass. **Recommendation: A**, plus the
collapsing border model and `::before` and `::after` if time allows, with B as
Phase 8's first CSS breadth item. The exit is one site; B doubles the phase.
With A, the README says which CSS is drawn, and a page that needs floats lays
out wrongly, inside the sandbox.

**(c) Fonts.** *Tables:* TrueType outlines need `head`, `hhea`, `hmtx`,
`maxp`, `loca`, `glyf`, `cmap`, `name`, `OS/2` and `post` (macOS's
`Verdana.ttf` has them, with `kern`, `GPOS`, `GSUB` and hinting tables;
measured). **C1:** TrueType only; a CFF-only face is skipped and its
characters fall back. **C2:** CFF too (Type 2 charstrings, an interpreter on
font bytes about the size of `glyf` and `cmap` together, with bounded stack
and subroutine depth); many CJK and Noto fonts are CFF. *Sources:* the
renderer cannot open a file once sandboxed (`(deny default)` with no file rule
in `crates/clazel-sandbox/src/seatbelt.rs`; no `open` or `openat` in
`syscalls.rs`), so fonts are read before it enters the sandbox (5.20). **S1:**
system fonts by known path (macOS `/System/Library/Fonts/` and
`Supplemental/`, where Verdana and Geneva are, measured; Linux
`/usr/share/fonts/` with DejaVu or Liberation where installed), a fixed family
table per OS, no enumeration and no fontconfig. **S2:** one bundled
open-licensed family (sans, serif, mono) in the binary for everything. **S3:**
both, system first, the bundled family as fallback and for every test. The
licence question: the repository is MIT; DejaVu (Bitstream Vera terms with
public-domain changes) and SIL Open Font License 1.1 fonts (Liberation, Noto)
may be bundled with software but keep their own licence, which must ship with
them; OFL forbids selling the font alone and reserves names on modification.
Whether a font file belongs in the repository and the binary is the
maintainer's call. *Shaping:* **H1:** Latin, Greek and Cyrillic with `cmap`,
`hmtx` and pair kerning (`GPOS` type 2, `kern`), no `GSUB`. **H2:** `GSUB` and
`GPOS` marks too, the start of complex shaping (Arabic and Indic also need the
Universal Shaping Engine's rules, an L item of its own). **Recommendation: C1,
S3, H1.** HN is Latin text in Verdana; other scripts fall back to whatever
system face maps them, unshaped, which is legible for CJK and wrong for Arabic
and Indic (listed). CFF and complex shaping go with web fonts to Phase 8. If
the bundled font is refused, tests use a font fetched by `scripts/` at a
pinned URL and checksum.

**(d) Raster.** **A:** a CPU rasterizer of our own at tier 1 (5.17): exact
area coverage, fixed point, Kani harnesses, in the sandbox, no new TCB. **B:**
the same at tier 0; cheaper by the harnesses, but page-controlled coordinates
in arithmetic are where a Tier 1 proof pays. **C:** GPU (Metal, Vulkan or
OpenGL, or `wgpu`): the sandboxed renderer cannot reach the GPU, so the work
moves to the host or a new GPU process, with drivers in the TCB and a binding
crate family shipped (rule 8 allows "GPU access"); the exit page is text and
rectangles, which a CPU draws in milliseconds. **Recommendation: A**, and no
GPU path in this phase.

**(e) The window.** *Bindings:* **W1:** raw platform APIs: on macOS, AppKit
and Core Graphics through `clazel-sys` (Objective-C runtime calls with
`objc_msgSend` declared once per message signature, a polling event loop so
that no class or callback is defined in Rust, a layer's contents set from a
`CGImage`; about 25 to 35 new foreign functions, each audited); on Linux, an
X11 client of our own in safe Rust over a Unix socket (5.22), no `unsafe` and
no dependency, with XWayland under Wayland. **W2:** a windowing crate shipped
(`winit` with `softbuffer`, or `minifb`), allowed by rule 8 as "OS and
windowing bindings"; less code of ours, but `winit` brings tens of crates on
Linux (Wayland and X11 bindings, `xkbcommon`, `calloop`) and the `objc2`
family on macOS, none under `clazel-sys`'s rules, and `minifb` compiles C or
Objective-C shims with `cc`. **W3:** W1 on macOS, W2 on Linux. *What the
renderer sends:* **P1:** a pixel surface (5.18): fonts, layout and raster stay
in the sandbox and the host copies pixels whose size the kernel checked.
**P2:** a display list the host rasterizes: smaller messages and host-side
scrolling, but the unsandboxed host then reads page-derived draw commands and
runs font and raster code on them. *The sandbox* is unchanged either way: the
renderer never owns a window (no `mach-lookup` for the WindowServer in its
Seatbelt profile, no `socket` or `connect` to reach an X server in its seccomp
list). **Recommendation: W1 and P1.** The audited `unsafe` count grows and the
README states it, but each call is one line under the existing rules and an
independent audit, where a windowing crate's `unsafe` would be trusted unread;
P1 keeps every byte a page chose in the sandbox until it is pixels. 5.21
includes the checker changes W1 needs.

**(f) The Phase 3 dependency.** The exit URL is `https://` only, and TLS is
not in the kernel's fetch (Dependencies, above). **Recommendation: state it as
a dependency, not Phase 5 work.** Everything is built and tested against
`http://` sites and the in-process server of 5.26 serving the HN-shaped
fixture; only the demo's last step waits, and exit criterion 3 says so. The
alternative, pulling 3.5b and 3.5e to 3.5g in, ties this phase's size to Phase
3's hardest items.

**(g) `clazel-text`.** **G1:** delete it with `Display` once the new pipeline
draws, converting its golden tests and `crates/clazel/tests/pages.rs` (1,761
documents' text) to box tree dumps (5.13). **G2:** keep it as `browse --text`,
which keeps `Display` and `Show` and every display theorem over two messages.
**G3:** keep it until 5.26 passes, then G1. **Recommendation: G3:** a second
display path doubles the theorems for little use, and a box tree dump is a
better golden test.

**(h) Style sheet fetches.** HN's only sheet is a `<link rel=stylesheet>`, a
sub-resource, which Phase 4 left to Phases 6 and 7. **F1:** build 5.19:
same-origin sheets with cookies, cross-origin sheets without credentials, a
listed deviation from Fetch's "no-cors" with "include" that keeps
`theorem_cookie_noninterference` as stated (no renderer receives a response
made with another site's cookies). **F2:** F1 with Fetch's credentials, which
needs the noninterference theorem restated with a declassification for
cross-site sub-resources (third-party cookies). **F3:** inline style only; HN
then gets the UA sheet and presentational hints (tables and colours) but not
its fonts, sizes or link colours. **Recommendation: F1:** it is the request
shape Phase 6's images and Phase 7's `fetch()` reuse, and its credentials rule
can be widened later with its own theorem.

**(i) Nested browsing contexts.** Phase 4 left the out-of-process `iframe`
design to this plan. **I1:** design only (5.24); `iframe` stays a link.
**I2:** build it here. **Recommendation: I1:** HN has no `iframe`, and the
kernel change is as large as 5.18 and belongs with Phase 7, when a frame can
script its parent.

### 5.1 Inventory and test data (M)

**Inventory.** A script in `scripts/` (run locally) fetches the exit pages and
the sheets they link and writes `docs/phase5-inventory.md`: element, attribute
and inline style counts per page, and every selector shape, property, value
type, unit and at-rule per sheet. It stores counts, never the pages or the
sheet (their copyright is Y Combinator's and its users'). It is rerun before
5.26; anything new joins 5.6's subset or its "parsed, no effect" list.

**Vendoring and conversion**, as in items 1.0, 3.3 and 4.1, each with a
`SOURCE.md` (URL, commit, SHA-256, licence) and a converter in
`xtask/src/testdata/` that fails if the format changes:

- Servo's `css-parsing-tests` (`src/css-parsing-tests/` of
  `servo/rust-cssparser`: `component_value_list.json`,
  `one_component_value.json`, `declaration_list.json`, `one_declaration.json`,
  `rule_list.json`, `one_rule.json`, `stylesheet.json`,
  `stylesheet_bytes.json`, `An+B.json`, `urange.json`, `color3*.json`) under
  `crates/clazel-css/tests/data/`, its JSON shapes (`["ident", "foo"]`,
  `["error", "invalid"]`, …) mapped to our types. Its licence is read when
  vendoring; if it forbids redistribution, the suite runs from a pinned
  download, as Apple's mapping files did in 4.1.
- WPT at the commit item 3.3 pinned: `css/css-syntax/`, `css/selectors/`,
  `css/css-cascade/`, `css/css-color/`, `css/css-values/`, `css/css-fonts/`,
  `css/mediaqueries/`, the `css/CSS2/` directories 5.25 names,
  `css/css-tables/`, `css/css-text/white-space/`,
  `css/css-text/line-breaking/` and `quirks/`. Parsing tests are
  testharness.js files calling fixed helpers (`test_valid_value`,
  `test_invalid_value`, `test_valid_selector`, `test_invalid_selector`, and
  `css-syntax`'s own); the converter extracts their literal arguments and
  counts a file with non-literal calls as "not run", never as a pass. Reftests
  are vendored with their references and `fuzzy` metas.
- Unicode `LineBreak.txt`, `LineBreakTest.txt` and `EastAsianWidth.txt` at one
  pinned version, as tables by `cargo xtask tables`.
- Test fonts: the bundled family of 5.0(c) and a few open-licensed files
  covering `cmap` formats 4 and 12, composite glyphs, `kern` and `GPOS`
  kerning, a `.ttc` collection and a CFF font, each with its licence.

Dev-dependencies for the differentials (`cssparser`, `selectors`,
`ttf-parser`, `read-fonts`, `rustybuzz`, and 5.17's rasterizer oracle) get
`test` rows in DEPENDENCIES.md with exact versions, measured dependency counts
and reasons; an unreasonable chain falls back to 4.11's pinned binary outside
the workspace.

### 5.2 CSS Syntax: input and tokenizer, spec and contracts (M)

`crates/clazel-css`, module `tokenizer/`. CSS Syntax Level 3, pinned to a
dated draft or commit: §3.2† "the input byte stream" (the fallback encoding
from the BOM, the protocol's `charset`, an `@charset "…";` rule as the exact
first bytes, the referring document's encoding, else UTF-8; then Encoding §6
"decode", already proven in `clazel-encoding`); §3.3† preprocessing (CR LF, CR
and FF to LF; U+0000 and surrogates to U+FFFD); §4.1† the token types (ident,
function, at-keyword, hash with its type flag, string, bad-string, url,
bad-url, delim, number, percentage and dimension with value and type flag,
whitespace, CDO, CDC, colon, semicolon, comma, the brackets, EOF;
unicode-range if the pinned text keeps it); and §4.3† the tokenizer
algorithms, one spec function each under the standard's name, steps numbered:
"consume a token", "consume comments", "consume a numeric token", "consume an
ident-like token", "consume a string token", "consume a url token", "consume
an escaped code point", "check if two code points are a valid escape", "check
if three code points would start an ident sequence", "… would start a number",
"consume an ident sequence", "consume a number", "convert a string to a
number", "consume the remnants of a bad url".

Modelling choices: the input is `Seq<u32>` after preprocessing, and
"reconsume" is not advancing (as 4.6); a number is kept as the parts "convert
a string to a number" reads and as an exact rational, never a float in the
spec (`clazel-style` converts once, with the rounding stated); parse errors
are not modelled; two faces, `tokenize(input)` and `next_token(state)`, proven
equal.

Proven, and seeded as mutations: `theorem_tokenizer_total` (each call consumes
a code point or emits EOF); `theorem_tokens_bounded` (at most one token per
code point plus EOF); `theorem_step_equals_whole`. Contracts: the exec
`next_token` equals the spec's and `tokenize` is its fold, with no recursion
in exec code.

### 5.3 CSS Syntax: the parser, spec and contracts (L)

`clazel-css`, module `parser/`. CSS Syntax §5†, one spec function per
algorithm, steps numbered: the token stream (§5.3†: "consume a token",
"discard whitespace", "process", mark and restore as an index); the entry
points (§5.4†: "parse something according to a CSS grammar", "parse a
stylesheet", "parse a stylesheet's contents", "parse a block's contents",
"parse a rule", "parse a declaration", "parse a component value", "parse a
list of component values", "parse a comma-separated list of component
values"); the algorithms (§5.5†: "consume a stylesheet's contents", "consume
an at-rule", "consume a qualified rule", "consume a block", "consume a block's
contents", "consume a declaration" with `!important` and the custom-property
case, "consume a list of component values", "consume a component value",
"consume a simple block", "consume a function"); §6† the An+B microsyntax; and
§9† serialization, which the tests compare. Output types are the standard's:
at-rules (name, prelude, optional block), qualified rules (prelude,
declarations, child rules) and declarations (name, component values, important
flag).

The text was restructured between 2021 and 2024 for nesting ("consume a
block's contents", the mark-and-restore stream); the spec follows the pinned
text, and the cases where `css-parsing-tests` (written for the 2014 text) and
`cssparser` expect the older behaviour are listed as expected failures and
differences.

Modelling choices: as 5.2; "parse something according to a CSS grammar" takes
the grammar as a parameter (component values to an option), so
`clazel-selectors` and `clazel-style` pass their own and this crate depends on
neither. Proven: `theorem_parse_total`; `theorem_parse_bounded` (the output's
component values number at most the input tokens, so parsing is linear);
`theorem_blocks_balanced` (each simple block closes on its opening token's
mirror or EOF). The exec parser iterates with an explicit stack: a CSS bomb is
`{` repeated, and Verus proves no panics, not no stack overflow.

### 5.4 CSS Syntax: implementation, independent transcription, conformance (L)

The exec tokenizer and parser over `&[u32]`, each function proven equal to its
spec function, as `clazel-html`'s tokenizer was.

Independent (`independent.rs`): CSS 2.1 §4.1.1 (the tokenizer as a lexical
grammar, a different text and form) and §4.2 with Appendix G† (the core
grammar and its error recovery), transcribed without reading `spec.rs`, proven
equal where the two texts decide the same, with the differences listed in the
lemma (CSS 2.1 differs on `<CDO>`/`<CDC>`, escapes, `url(`, exponents, and has
no nesting), as `clazel-http` listed RFC 7230 against RFC 9112.

Conformance (`tests/conformance_syntax.rs`): every `css-parsing-tests` file
through its entry point; the WPT `css-syntax` cases 5.1 extracts; a
differential against Servo's `cssparser` on random and mutated sheets and
every vendored sheet, comparing tokens and rule structure. Mutations: one or
more per algorithm (a dropped case, an escape not consumed, `!important`
missed, a block closed by the wrong token), certified by example. Under Miri:
the JSON suites whole if they take under a minute, else a stated stride.

After 5.2 to 5.4: **raise `clazel-css` to tier 2** (if 5.0(a) chooses it).

### 5.5 Selectors: parsing, matching, specificity (L)

`crates/clazel-selectors`. Selectors Level 4, pinned: the grammar†
(`<selector-list>`, `<complex-selector>`, `<compound-selector>` and their
parts; pseudo-elements parsed and matching nothing), parsed through 5.3's
grammar entry point and the API hook "parse a selector"†; type, universal and
namespace selectors (§5†); attribute selectors (§6†: `[a]`, `=`, `~=`, `|=`,
`^=`, `$=`, `*=`, the `i` and `s` flags, class selectors as `[class~=v]`); ID
selectors (§7†); `:link`, `:visited`, `:any-link` (§9†); `:root`, `:empty`,
`:first-child`, `:last-child`, `:only-child`, `:nth-child(An+B)` and the
`-of-type` forms (§15†); `:is()`, `:not()`, `:where()` (§4†) but not `:has()`;
the four combinators (§16†); specificity (§17†); and "match a selector against
an element"† over `clazel-dom`'s exec arena, through its readers only.
Serialization (CSSOM "serialize a selector"†) for the WPT parsing cases.

Modelling choices: `:visited` never matches (no history reaches a renderer,
which also closes the history-sniffing channel); `:hover`, `:active` and
`:focus` never match in this phase; in quirks mode, class and ID selectors
match ASCII case-insensitively (Selectors §6.6† and §7†); HTML element and
attribute names match as HTML's case rules say; `:has()` is out because its
matching is not linear (Phase 8).

Proven: `theorem_parse_total`; `theorem_match_total` with a work bound (one
complex selector against one element visits at most depth × compounds
elements, so a rule set costs at most rules × elements × depth × compounds,
which 5.26's CSS bomb measures); `theorem_specificity_monotone` with the
standard's specificity examples evaluated; `:where()` contributes zero and
`:is()` its most specific argument. Independent: CSS 2.1 §5† and §6.4.3
(selectors and specificity) transcribed without reading `spec.rs`, proven
equal on the CSS 2.1 subset. Conformance (`tests/conformance_selectors.rs`):
the WPT parsing cases; the `css/selectors/` reftests through 5.25 once the
pipeline draws; a differential against Servo's `selectors` crate (through a
small test DOM adapter) on random selectors and random trees built by
`clazel-treebuilder`. Mutations per simple selector, combinator, specificity
rule and the quirks rule. Raise to tier 2 after the proof, the transcription
and the suites.

### 5.6 Property values for the subset (L)

`crates/clazel-style`, module `values/`. For each property of the subset
(5.0(b)), its value grammar from its defining specification, parsed through
5.3's grammar entry point: CSS Values 4 (`<length>` in `px`, `pt`, `pc`, `in`,
`cm`, `mm`, `Q`, `em`, `ex`†, `rem`; `<percentage>`, `<number>`, `<integer>`;
the CSS-wide keywords); CSS Color 4 (hex in 3, 4, 6 and 8 digits, named
colours, `rgb()`, `rgba()`, `hsl()`†, `transparent`, `currentcolor`); CSS 2.1
and CSS Box 3 for margins, padding, borders (every style parsed, drawn
`solid`, listed), widths and heights with their `min-` and `max-`; CSS Display
3 for `display` (`none`, `block`, `inline`, `inline-block`, `list-item`, the
table values); CSS 2.1 §11 for `overflow` and `visibility`; CSS Fonts 3 §3†
for `font-family`, `font-size` (with the keyword table HTML's legacy font
sizes map to), `font-weight`, `font-style` and `font`; CSS 2.1 §10.8 and §16
with CSS Text 3 for `line-height`, `vertical-align`, `text-align`,
`text-decoration`, `text-indent`, `white-space`, `overflow-wrap`,
`word-break`; CSS Backgrounds 3 for `background-color` and the `background`
shorthand's colour; CSS 2.1 §17 for `border-spacing`, `border-collapse`,
`table-layout`; `list-style-type`. Shorthands expand as their definitions say.
The properties HN uses but this phase does not apply (`cursor`,
`pointer-events`, `resize`, `transform`, `page-break-before`, `text-overflow`,
background images) are "parsed, no effect", listed in the README; anything
else is dropped as invalid, as CSS Syntax says. In quirks mode, the Quirks
Mode Standard's hashless hex colour and unitless length quirks (§3.1†, §3.2†)
apply to the properties it lists.

Kani (tier 1): every value parser on every token sequence up to a stated
length returns without panic or overflow; numeric conversion (rational to
fixed point, units to `px`) never overflows, with out-of-range values clamped
to a stated range (lengths in 1/64 px as `i32`; CSS Values 4 allows an
implementation range†). Conformance (`tests/conformance_values.rs`): the WPT
parsing cases 5.1 extracts for the subset's properties, compared on CSSOM's
serialization†; other properties are counted as not run.

### 5.7 The cascade, inheritance and computed values (L)

`clazel-style`, module `cascade/`. CSS Cascade 4, pinned: §6.1† the cascade
sorting order (origin and importance, context, element-attached styles,
specificity, order of appearance; one encapsulation context, as there are no
shadow trees); §6.2† origins (user agent, an empty user origin, author) and
§6.3† important declarations; §6.4† with CSS 2.1 §6.4.4, presentational hints
at author level with specificity zero, before every author rule; §4† value
processing (declared, cascaded, specified, computed; used values are
layout's); §7† defaulting (initial values, inheritance, `initial`, `inherit`,
`unset`, `revert`). Computed values as each property's definition table says
(lengths to `px`, `em` against the parent's computed `font-size`,
`currentcolor` resolved for `color`).

The user agent style sheet is HTML §15's, transcribed into `data/ua.css` from
the pinned HTML commit (§15.3.1 hidden elements, §15.3.3 flow content,
§15.3.4† phrasing content, §15.3.6 sections and headings, §15.3.7 lists,
§15.3.8 tables with its quirks-mode rules, §15.3.10 form controls, §15.3.11
`hr`, and the parts of §15.4 that size replaced elements), parsed by our
parser and checked by `cargo xtask tables` against the vendored text.
Presentational hints are §15.3's and §15.4's attribute mappings: `bgcolor` and
`color` through "rules for parsing a legacy colour value" (§2.3.6†), `width`
and `height` through "rules for parsing dimension values" (§2.3.4.4†),
`align`, `valign`, `border`, `cellpadding`, `cellspacing` (§15.3.8), `font
size` through "rules for parsing a legacy font size" (§15.3.4†), and `center`
and `align=center` centring block-level descendants (§15.3.3), which no CSS
property expresses (listed, with layout's effect). The output is a side table
of computed values indexed by node id.

Kani (tier 1): the sort and the inheritance walk never panic for any rule list
and tree up to a stated size; the walk is iterative. Conformance: WPT
`css-cascade` reftests through 5.25, and a golden table of computed values for
4.1's vendored documents under the UA sheet, reviewed as fixtures. A Verus
spec of the sort order is welcome and is where a later tier 2 would start.

### 5.8 Style sources and media queries (M)

`clazel-style`, module `sources/`, and the renderer's use of it. What style
sheets a document has, in order, as HTML and CSSOM say: `<style>` elements'
child text ("update a `style` block", HTML §4.2.6†), `<link rel=stylesheet>`
elements' fetched sheets (HTML's link type "stylesheet" and its "fetch and
process the linked resource" steps†: in quirks mode a same-origin sheet whose
`Content-Type` is not `text/css` is still used, otherwise it is not), and each
element's `style` attribute (CSS Style Attributes §3†: the value parsed as a
block's contents, its declarations in the element-attached context). The
`media` attribute and `@media` rules: Media Queries 4† for `all`, `screen` and
`print` media types, `not` and `only`, `and`, comma lists, and the `width`,
`height`, `min-`/`max-` forms and `orientation` features against the viewport;
any other feature is unknown and makes its query false (Media Queries 4's rule
for unknown features†), which is the effect `min-device-pixel-ratio` and
`-webkit-min-device-pixel-ratio` get (the second is defined by the
Compatibility Standard†, and HN's rule under it only changes a background
image's size, which this phase does not draw). `@import`, `@supports`,
`@font-face`, `@namespace` and `@page` are recognised and ignored, listed.

Kani: the media query evaluator on every query up to a bound. Tests: the WPT
`mediaqueries/` cases for the features above, extracted by 5.1; unit tests per
source.

### 5.9 Font file and table parsing (L)

`crates/clazel-font`. The OpenType specification (Microsoft, the version
pinned in the header), by chapter: "The OpenType font file" (the table
directory: `sfntVersion` `0x00010000` or `OTTO`, `numTables`, the table
records; the collection header `ttcf`, since macOS ships `.ttc` files such as
Helvetica and Menlo†); `head` (`unitsPerEm`, `indexToLocFormat`); `hhea`
(ascender, descender, line gap, `numberOfHMetrics`); `hmtx`; `maxp`
(`numGlyphs`); `loca`; `glyf` (simple glyphs with their flag repeats and short
vectors; composite glyphs with offsets or anchor points and their scale
forms); `cmap` (encoding records preferring the full Unicode repertoire;
formats 4 and 12, and 0 and 6 if the test fonts need them); `name` (IDs 1, 2,
16, 17, UTF-16BE); `OS/2` (`usWeightClass`, `fsSelection`, typo metrics with
`USE_TYPO_METRICS`); `post` (`isFixedPitch`, underline metrics); `kern`
version 0 format 0; and `GPOS` LookupType 2 (formats 1 and 2) for the `kern`
feature, with the Common Table Formats it needs (ScriptList, FeatureList,
LookupList, Coverage and ClassDef formats 1 and 2, ValueRecord, LookupType 9
extension). Out unless 5.0(c) takes them: `CFF `/`CFF2`, `GSUB`, `gvar`/`fvar`
(a variable font is read at its default instance), colour and bitmap tables,
and every TrueType instruction table (no hinting, so no bytecode interpreter
ever runs on font bytes).

Form: each table is parsed from the slice its record gives, every offset and
length checked against that slice and the record against the file; glyphs are
decoded on demand, so a font is never expanded beyond a stated bound; a
checksum mismatch is recorded, not fatal (listed).

Kani (tier 1): the directory and each table parser on every byte string up to
a stated length, and with symbolic offsets over a larger fixed buffer so
offsets near the end are covered; `loca` with `glyf` on symbolic glyph
indices; no panic, no overflow, no read outside the slice. Independent
evidence: Apple's TrueType Reference Manual describes the same tables from
another body, and its and the OpenType chapters' worked examples are unit
tests. Differential (`tests/conformance_fonts.rs`): `ttf-parser` and
`read-fonts` on every vendored font, every font under the runner's system font
directories (ignored under Miri: it opens files) and 10,000 mutated fonts,
comparing the directory, metrics, every mapped `cmap` entry, outlines point by
point and kerning pairs; expected differences listed.

### 5.10 Glyph outlines and font matching (M)

`clazel-font`, module `outline/`, and `clazel-layout`, module `fonts/`.
Outlines: a `glyf` glyph to contours of on-curve and off-curve points, with
the implied on-curve midpoints between consecutive off-curve points made
explicit, composite glyphs flattened with their transforms to a stated nesting
depth (a component cycle or depth beyond the bound is an empty glyph, listed,
for the hostile font of 5.26), scaled from font units to pixels in fixed point
(26.6, as FreeType's convention, a listed choice) at the used font size. The
outline type is `clazel-raster`'s path input, so 5.17 can start with it alone.

Font matching, in `clazel-layout`: CSS Fonts 3 §5.2† "matching font styles"
over the font table 5.0(c) gives (family name to faces with weight, width and
style), with the generic families `serif`, `sans-serif` and `monospace` mapped
per OS (5.0(c)); then per character, §5.4†'s character handling: the first
face in the `font-family` list whose `cmap` maps the character, then the
fallback list, then `.notdef` of the first face. Kani: outline decoding on
symbolic glyphs (5.9's harness extended). Tests: outlines against
`ttf-parser`'s; matching unit tests per rule.

### 5.11 Shaping: characters to positioned glyphs (M)

`clazel-layout`, module `shape/`, over `clazel-font`. Scope per 5.0(c); as
recommended: a run of characters with one computed font to glyphs through
`cmap`, one glyph per character (no `GSUB`, so no ligatures; CSS Fonts'
default `font-variant-ligatures: normal` asks for `liga`, a listed deviation),
advances from `hmtx` scaled to the used size, kerning from `GPOS` type 2 for
the `kern` feature when the font has `GPOS` (Verdana on macOS has `GPOS`,
`GSUB`, `GDEF` and `kern`, measured 2026-10-31) and from `kern` otherwise, and
`letter-spacing` and `word-spacing` if 5.0(b) has them. Combining marks are
placed at the base's advance with zero advance (no `mark` feature; listed).
Right-to-left runs are drawn in logical order (no UAX #9; listed, Phase 8).
Positions are in 26.6 fixed point, with no hinting.

Tests: a differential against `rustybuzz` (a `test` row) with the `kern`
feature only and `liga` off, on Latin, Greek and Cyrillic text in every
vendored and system font present: the glyph ids and advances must agree
exactly; expected differences listed. Unit tests: the OpenType chapters' pair
kerning examples.

### 5.12 White space and line breaking (M)

`clazel-layout`, module `text/`. CSS Text 3 (pinned): §3† the `white-space`
property and its values `normal`, `pre`, `nowrap`, `pre-wrap`, `pre-line`;
§4.1† phase I, collapsing and transformation (segment breaks, collapsible
spaces and tabs), and §4.2† phase II, trimming and positioning at line starts
and ends, hanging of preserved spaces in `pre-wrap`; §5† line breaking and
word boundaries with `word-break` (`normal`, `break-all`, `keep-all`, and the
legacy `break-word` that HN uses, which CSS Text 3 defines as `normal` with
`overflow-wrap: anywhere`†) and §5.5† `overflow-wrap` (`normal`, `break-word`,
`anywhere`, which also affects min-content sizing and so the table layout of
5.15). Line break opportunities from UAX #14 (pinned Unicode version): the
line breaking classes from `LineBreak.txt` with the class resolution of LB1
(AI, SG, XX to AL; SA, CJ per the standard's tailoring defaults), and the pair
rules LB2 to LB31 in order, transcribed rule by rule with the rule numbers in
comments; mandatory breaks for preserved segment breaks. `text-transform` is
not in the subset.

Tests (`tests/conformance_linebreak.rs`): every line of `LineBreakTest.txt`
through the rules (passing / total, the standard's tailorings that CSS asks
for, if any, listed as expected differences); the WPT `css-text/white-space/`
and `css-text/line-breaking/` reftests 5.25 runs. Under Miri: a stride of the
test file. The rules are a pure function and small; a Kani harness over
strings of a bounded length is welcome.

### 5.13 The box tree (M)

`clazel-layout`, module `boxes/`. From the DOM and the computed style table to
a box tree in an arena, iteratively: CSS 2.1 §9.2† (block-level and
inline-level boxes, anonymous block boxes around inline content in a block
that also holds blocks, anonymous inline boxes), §9.7† (display, position and
float: positioning and floats are not in the subset, so `position` and `float`
compute and are ignored, listed), CSS Display 3's `display: none` (no box) and
`contents`† (out); list items (§12.5†, a marker box with `list-style-type`);
CSS 2.1 §17.2.1† anonymous table objects (the three passes: remove irrelevant
boxes, generate missing child wrappers, generate missing parents), so that
HN's `<tr style='height:10px'/>` and stray text in tables produce the
standard's boxes; replaced elements (HTML §15.4†: `img` with its `width` and
`height`, sized and drawn empty, Phase 6; `input` and `textarea` as boxes of
the size HTML §15.5† suggests from `size`, `cols` and `rows`, drawn as an
empty bordered box; `iframe` as a box with its link, 5.24). Text nodes become
text runs after 5.12's phase I.

Input: computed style is a parameter (`StyleFns`: a function from node id to
the subset's computed values), so this item and 5.14 to 5.16 are built and
tested with hand-written tables before 5.7 lands. Tests: golden box tree dumps
for the html5lib tree-construction documents of 4.1 under the UA sheet,
reviewed as fixtures (this replaces `clazel-text`'s golden test, 5.0(g)); and
the anonymous-table WPT reftests.

### 5.14 Block and inline formatting (L)

`clazel-layout`, module `flow/`. CSS 2.1 §8.3.1 collapsing margins (negative
margins included, which HN's `margin-bottom:-10px` needs); §9.4.1 block
formatting contexts (established by `overflow` other than `visible`,
`inline-block` and table cells); §9.4.2 inline formatting contexts and line
boxes; §10.3.3† block widths and margins (the over-constrained rule), §10.3.2†
and §10.3.4† replaced elements, §10.3.9† inline-block shrink-to-fit
(§10.3.5†); §10.4 and §10.7 `min-`/`max-` widths and heights; §10.6.3† and
§10.6.7† block and BFC-root heights; §10.8 line height (leading, the strut,
`vertical-align` keywords and lengths), with the Quirks Mode Standard's line
height calculation and blocks-ignore-line-height quirks (§3.3†, §3.4†); §16.1
`text-indent`; §16.2 `text-align` (`justify` drawn as `left`, listed); 5.7's
`center` behaviour; the html-fills-viewport and body-fills-html quirks (§3.6†,
§3.7†). Lines break at 5.12's opportunities with 5.11's widths. Content that
does not fit overflows; `overflow: hidden` clips in 5.16.

Form: widths top down and heights bottom up over the arena with an explicit
stack; lengths in 1/64 px as `i32` with saturating arithmetic (the workspace
denies `arithmetic_side_effects`); the result is a fragment tree (boxes with
positions and sizes, line boxes with positioned glyph runs) keyed by box id,
mapping back to node ids for hit testing. The whole document is laid out again
when the viewport width changes.

Tests: WPT `CSS2/normal-flow`, `margin-padding-clear`, `box-display`,
`linebox`, `visudet`† and `visuren`† reftests through 5.25; unit tests per
rule; the hostile layouts of 5.26.

### 5.15 Table layout (L)

`clazel-layout`, module `table/`. CSS 2.1 §17: §17.2 the table model with
5.13's anonymous objects, §17.3† columns, §17.4† captions, §17.5† layout with
§17.5.2.1 fixed and §17.5.2.2 automatic table layout, §17.5.3 height, §17.5.4
horizontal alignment, §17.6.1 separated borders (§17.6.2 collapsing if 5.0(b)
takes it). The grid comes from HTML's table processing model† ("forming a
table", with `colspan` clamped to 1000 and `rowspan` to 65534 as HTML's `td`
says†).

CSS 2.1's automatic layout algorithm is non-normative†, engines differ, and HN
uses it everywhere (no `table-layout: fixed`). So the spec followed is CSS
Tables Level 3 (Editor's Draft, pinned)'s "computing column measures" and
"distributing width to columns"†, which describe what engines converged on;
where it is unstable, the choice is listed and checked against 5.25's
reference engine. The Quirks Mode Standard's table cell quirks (§3.8† to
§3.10†) apply in quirks mode. Also: percentage widths (`#hnmain` at 85%),
`min-width` on tables (`796px`), `cellpadding` as cell padding, `cellspacing`
as `border-spacing`, `valign` as cells' `vertical-align`.

Tests: WPT `CSS2/tables` and the `css-tables` reftests (most of `css-tables`
needs JavaScript and is counted as not run); the HN-shaped fixture against the
reference geometry; 5.26's hostile tables.

### 5.16 Paint: the display list (M)

`clazel-layout`, module `paint/`. From the fragment tree to a display list:
CSS 2.1 Appendix E.2† painting order, reduced to what the subset creates (no
positioned elements, no floats, no `z-index`: the root stacking context only,
so for each block in tree order its background and borders, then its in-flow
blocks, then its inline content: backgrounds, borders, text, decorations),
backgrounds (§14.2† `background-color`, painted to the border box; the root
and `body` background propagated to the canvas as §14.2† says), borders
(§8.5†, every style drawn as `solid`, listed), text runs (positioned glyphs
with a colour), `text-decoration` lines (§16.3.1†: underline at the font's
`post` underline position), `overflow: hidden` clips (§11.1.1†, a clip
rectangle), `visibility: hidden` (painted nothing, still laid out), replaced
boxes (nothing: the image item exists for Phase 6), and hit regions (each
link's fragments with its resolved URL, for 5.18's clicks). The display list
is a flat list of items in paint order, each with integer device-pixel bounds,
so 5.17 rasterizes only the items that intersect the viewport and a scroll
re-rasterizes without a relayout.

Tests: unit tests per item kind; the WPT `CSS2/colors`, `backgrounds`† and
`text` reftests through 5.25's harness.

### 5.17 Raster (L)

`crates/clazel-raster`, per 5.0(d); as recommended, a CPU rasterizer of our
own, target tier 1. Inputs: a surface size and a scale (1, or 2 for HiDPI), a
clip stack of integer rectangles, and items: fill a rectangle; fill a path
(closed contours of lines and quadratic Béziers in 26.6 fixed point, exactly
the `glyf` outline form) under the non-zero rule; draw a glyph (a path, cached
as a coverage mask per glyph, size and quarter-pixel offset). Method, each a
listed choice: Béziers flattened within a quarter pixel; exact-area coverage
accumulated per scanline (the signed-area method of `font-rs` and
stb_truetype's second rasterizer), clamped to [0, 1], which equals non-zero
winding except where contours overlap with opposite orientation; source-over
blending in 8-bit sRGB, premultiplied, without gamma correction. Output: RGBA8
premultiplied rows.

Kani (tier 1): for every path up to a stated number of segments with any 26.6
coordinates in `i32`, and every surface up to a stated size, flattening and
accumulation never panic, overflow or index out of bounds, every coverage is
in [0, 255], and the blend never overflows. Tests: unit tests per primitive;
every vendored font's glyphs at 8 to 72 px against `tiny-skia` or
`ab_glyph_rasterizer` (a `test` row) within one coverage level per pixel, with
the difference histogram reported; Miri on 64×64 surfaces only, stated in the
tests. No GPU path unless 5.0(d) decides otherwise.

### 5.18 The IPC schema and the kernel: surfaces, viewports and input (L)

`clazel-ipc`: the schema changes. Tags are never reused; `Display` is retired
and tag 10 stays unused.

| Tag | Direction | Message | Fields |
|-----|-----------|---------|--------|
| 11 | renderer to kernel | `Surface` | title (text), width, height (unsigned) |
| 12 | renderer to kernel | `SurfaceRows` | bytes (RGBA8 premultiplied rows, at most `max_body_chunk`) |
| 13 | renderer to kernel | `SurfaceEnd` | |
| 108 | kernel to renderer | `Viewport` | width, height (device pixels), scale (1 or 2) |
| 109 | kernel to renderer | `Input` | kind (click, scroll, key), x, y, scroll delta as a sign (bool) and magnitude (the CBOR profile has no major type 1: `crates/clazel-ipc/src/cbor/spec.rs`), key |

`clazel-kernel`: per tab, a viewport, set by a new host event `Resize { tab,
width, height, scale }` and forwarded as `Viewport` to the tab's renderer and
to any it later spawns; per renderer, a pending surface (the header and the
rows so far, refused beyond `width × height × 4` bytes). On `SurfaceEnd` with
exactly that many bytes, and `width` and `height` at most the tab's viewport,
the output is `Paint { tab, url, title, width, height, pixels }`, `tab` and
`url` from kernel state; anything else (too large, too short, rows with no
header, an uncommitted renderer) is a disallowed frame under item 2.10's
rules. A new host event `Input { tab, input }` becomes a `ToRenderer` for that
tab's renderer only. `Show` retires with `Display`.

Theorems, each with certified mutations: `theorem_paint_only_own_tab` (a
renderer's frames give at most one `Paint`, for its own tab, and no other
output); `theorem_address_bar_integrity` restated (`Paint.url` is the
committed URL of the renderer the frames came from, for every message
content); `theorem_paint_fits_viewport` (`width` and `height` at most the
tab's viewport and `pixels.len() == width × height × 4`);
`theorem_paint_is_the_surface` (the pixels are the renderer's rows since its
`Surface`, in order); `theorem_input_only_to_own_tab`; the Phase 2 to 4
theorems restated with `Paint`, `Resize` and `Input` in the observations.
Clicks: the renderer hit-tests 5.16's regions and sends the existing
`Navigate`, which item 2.11 already treats as the user's. Scrolling: the
renderer keeps the offset and repaints on `Input`.

Pixels travel over the socket and through the kernel's exec copy, simple and
proven: a 1280×800 surface at scale 1 is 4,096,000 bytes, four frames. 5.26
measures repaint time; a shared-memory surface (`memfd_create`/`mmap`,
`shm_open`/`mmap`: new audited `clazel-sys` calls and sandbox rules, and the
seccomp list deliberately has no `recvmsg` for descriptor passing) is a later
decision, not this item's.

### 5.19 The kernel: style sheet fetches (L)

Phase 4 left page-started fetches to later phases; HN's `<link
rel=stylesheet>` makes one necessary now (5.0(h)). `clazel-ipc`:

| Tag | Direction | Message | Fields |
|-----|-----------|---------|--------|
| 14 | renderer to kernel | `FetchStyle` | request (unsigned, the renderer's id for it), url (text) |
| 110 | kernel to renderer | `StyleResponse` | request, content type (bytes) |
| 111 | kernel to renderer | `StyleBody` | request, bytes |
| 112 | kernel to renderer | `StyleEnd` | request |
| 113 | kernel to renderer | `StyleFailed` | request |

`clazel-kernel`: a committed renderer's `FetchStyle` is resolved against its
committed URL and run as Fetch's request for a `<link rel=stylesheet>` without
`crossorigin` (destination "style", mode "no-cors"†) by the same 3.6
transducer navigations use, in `Renderer::subfetches`, with a stated limit at
once and per document, on connections owned by the tab with the renderer's
domain as partition key. Credentials per 5.0(h): same-origin requests carry
the jar's cookies and store `Set-Cookie`; cross-origin ones do neither
(listed). Redirects follow 3.6's rules, each hop's origin deciding its
credentials. A navigation ends the old document's sub-fetches; a `Tick` past a
stated timeout fails one.

Theorems: `theorem_subfetch_only_to_requester` (every `Style*` frame for a
request goes to the renderer that sent it, and only while it is committed to
the same document); `theorem_subfetch_credentials` (a sub-fetch's `Send`
carries jar-derived octets only if its URL is same-origin with the renderer's
lock; 3.6's `theorem_wire_cookies` carried through);
`theorem_connection_ownership` and noninterference restated over sub-fetches.
Mutations for each decision (credentials sent cross-origin, a response to
another renderer, a sub-fetch surviving a navigation, each limit). Tests in
`tests/fetch.rs`; through processes in 5.26.

### 5.20 The renderer pipeline (M)

`clazel-renderer`, `pipeline.rs` extended, Tier 0: after 4.13's steps 1 to 4
(content type, encodings, parse, base URL), collect the style sources in tree
order (5.8), send a `FetchStyle` for each `<link rel=stylesheet>` whose
`media` matches, and wait for all to end or fail (render-blocking, as HTML
says for style sheets in `head`†; a sheet that never answers is failed by the
kernel's timeout on `Tick`); decode each sheet (5.2's §3.2), parse (5.3),
cascade (5.7) into the computed table, build boxes (5.13), lay out at the
viewport width (5.14, 5.15), build the display list (5.16), rasterize the
viewport at the scroll offset (5.17), and send `Surface`, `SurfaceRows`,
`SurfaceEnd`. On `Viewport`: lay out again and repaint. On `Input`: scroll
(clamped to the page) and repaint, or hit-test a click and send `Navigate`.
`text/plain` documents become one `pre` block styled by the UA sheet; other
types show the notice, drawn.

Fonts: the renderer reads the font files of 5.0(c)'s table **before** it
enters the sandbox (the host passes the paths on the command line; the
Seatbelt profile and the seccomp allowlist then forbid opening any file, as
today: `crates/clazel-sandbox/src/seatbelt.rs` and `syscalls.rs`), so no
sandbox rule is added for fonts. The memory bound of 4.13 is extended by the
style sheets (at most the body limit each, and the per-document count), the
computed table (one record per node), the box and fragment arenas (a constant
per node and per glyph), the display list and one surface; stated in the crate
README with its numbers and measured by 5.26. The renderer stays
single-threaded (no `clone` in the seccomp allowlist).

### 5.21 The window on macOS (L)

Per 5.0(e); as recommended, through `clazel-sys` in the audited style: each
new foreign function is added to `xtask/src/sys.rs`'s list and called in one
`unsafe` block with a `// SAFETY:` comment citing Apple's documentation and
header; the checker learns to accept Apple citations (as `cites_win32_docs`
accepts Microsoft's) and several `#[link_name = "objc_msgSend"]` declarations,
one per message signature, each listed by name. The calls: the Objective-C
runtime (`objc_getClass`, `sel_registerName`, typed `objc_msgSend`) for
`NSApplication` (`sharedApplication`, `setActivationPolicy:`,
`finishLaunching`, `nextEventMatchingMask:untilDate:inMode:dequeue:`,
`sendEvent:`: a polling loop, so no class or callback is defined in Rust),
`NSWindow` (create, title, content view, close), the view's layer with
`contents` set to a `CGImage` from Core Graphics
(`CGColorSpaceCreateDeviceRGB`, `CGDataProviderCreateWithData`,
`CGImageCreate` and their releases), and `NSEvent`'s accessors for location,
buttons, scroll deltas, key codes and characters. No policy lives in
`clazel-sys`; `clazel-window` decides what to open and what an event means.

Every change is audited by another session (CLAUDE.md rule 1); the author
leaves the audit step failing and says so in the pull request, and the README
states the new `unsafe` count. Tests: a smoke test that opens and closes a
window (ignored under Miri and without a display, with the reason);
`clazel-window`'s event translation on recorded events.

### 5.22 The window on Linux (L)

Per 5.0(e); as recommended, an X11 client of our own in safe Rust in
`clazel-window`, speaking the X Window System Protocol (X11R7, the document
pinned) over the Unix socket `DISPLAY` names, so no `unsafe` and no shipped
dependency: connection setup with `MIT-MAGIC-COOKIE-1` from the `XAUTHORITY`
file (whose format we parse), `CreateWindow`, `ChangeProperty` for the title
and `WM_DELETE_WINDOW`, `MapWindow`, `CreateGC`, `PutImage` in `ZPixmap`
format split to the maximum request length (`BIG-REQUESTS` if offered), and
the events `Expose`, `ConfigureNotify`, `ButtonPress` (buttons 4 and 5 are the
wheel), `KeyPress` with `GetKeyboardMapping`, `ClientMessage`. Wayland
sessions use XWayland; a native Wayland client needs shared memory passed as a
descriptor, which stable `std` cannot send, so it is Phase 8. The X server's
replies are parsed by our code at Tier 0 in the host: the server is in the TCB
(it sees every pixel already), and every read is bounds-checked under the
workspace lints.

Tests: the encoder and reply parser against recorded exchanges; a smoke test
against `Xvfb` in CI's Linux job if the image has it (else ignored, with the
reason).

### 5.23 `clazel browse` with a window (M)

`crates/clazel/cli/browse.rs` and `clazel-window`: open a window, a tab at the
URL, and loop on window events and kernel outputs. The window is two regions
the host composes: an address bar strip at the top, drawn by the host from
`Paint.url` (and an edit field when the user types a URL), and the content
area below it, where the latest `Paint` for the tab is copied, clipped to the
content area (its size is already at most the viewport, 5.18). The host draws
its own text (the address bar) with `clazel-font`, `clazel-layout`'s shaping
and `clazel-raster` on a bundled or system font, outside the sandbox; it never
draws a byte the page chose in the strip. The page's title (from
`Paint.title`) goes to the window's title bar, after the URL, so that a title
cannot look like the address. Events: a resize sends `Resize`; a click or
wheel in the content area sends `Input` with coordinates relative to it; keys:
typing in the address bar and Enter navigate (`navigate_tab`), Escape cancels,
`Cmd/Ctrl-L` focuses it, `Cmd/Ctrl-[` goes back along the host's list of
committed URLs, `Cmd/Ctrl-R` reloads, Space, Page Up/Down and the arrows
scroll (sent as `Input`). The host shell (`crates/clazel/src`) gains only the
routing of `Paint`, `Resize` and `Input` and stays under 300 lines; the window
and the loop live in `clazel-window` and `cli/`.

`browse --headless OUT URL` renders one page to a file without a window, as a
PPM or a PNG with stored (uncompressed) deflate blocks, both written by our
own code (rule 8); the reference harness (5.25) and CI use it.

### 5.24 Nested browsing contexts: design (S)

Phase 4 left this design to Phase 5. A design note in this file (an appendix),
not code, recommended in 5.0(i): an `iframe` of another origin is another
renderer under the one-renderer, one-origin rule; the kernel gains a frame
tree per tab (each frame a renderer, its parent, and the rectangle the
parent's layout gave it, sent by the parent as a message); the host composes
the child's `Paint` into that rectangle, clipped, and the kernel proves that a
child's surface is placed only inside the rectangle its parent assigned and
that a parent never receives a child's pixels or input. Same-origin iframes
may share the parent's renderer. What the theorems become
(`theorem_paint_fits_viewport` per frame, address bar integrity unchanged: the
address is the top-level frame's) and what it costs (a kernel state change as
large as 5.18). Until it is built, an `iframe` is a box showing its resolved
URL as a link.

### 5.25 Reference rendering harness and reftests (M)

`crates/clazel/tests/reftests.rs` and `xtask`. **Reftests:** each vendored WPT
reftest and its reference (`<link rel=match>` or `mismatch`) are rendered by
`browse --headless` at 800×600, scale 1, with the bundled font for the generic
families (so the runner's fonts do not matter), and compared pixel by pixel; a
`<meta name=fuzzy>` gives the allowed maximum difference and pixel count, and
nothing else is tolerated. A reftest compares our engine with itself on two
equivalent pages, which is how WPT is designed and why it is honest without a
second engine. Tests needing JavaScript, images or features outside the subset
are counted as not run, by reason; the pass count is a conformance row in the
README table.

**Reference engine for the exit pages.** A script in `scripts/` (run locally)
loads a page in a pinned headless Chrome or Firefox at a fixed viewport with
the same font files, and records a screenshot and every text node's and
element's client rectangles (the browser's own `getClientRects`) as JSON, with
the browser's name, version and date. Our side dumps the same rectangles from
the fragment tree. The comparison is **geometry first**: every text run's box
within a stated tolerance (for instance 2 px in position and 2 % in width, set
once and never loosened), with the count outside it reported; the **pixel
difference** (changed pixels, mean difference) is reported, never asserted,
because engines rasterize fonts differently by design. Our own screenshot of
the HN-shaped fixture is stored and compared exactly in CI as a regression
test.

### 5.26 Exit demo, hostile pages, process tests (M)

- **Demo:** `cargo run -p clazel -- browse https://news.ycombinator.com/` on
  macOS arm64 and Linux x86-64 (X11 or XWayland) once Phase 3's TLS is in the
  kernel: the front page, a Show HN item page, a click, scrolling, back;
  5.25's geometry and pixel numbers recorded in the Status table. Before that:
  `http://` sites and the fixture.
- **The HN-shaped fixture:** a page and a sheet written for this project (MIT,
  so they can be vendored and screenshotted) with 5.1's measured shapes
  (quirks mode, the nested tables, presentational attributes, spacer images,
  `font` elements, the inline styles, selectors, properties and media queries)
  and invented text. The real pages and `news.css` are not vendored.
- **Through real processes:** an in-process server serves the fixture; a test
  drives `browse --headless` and the kernel: the sheet arrives through
  `FetchStyle` with the page's cookie, a cross-origin sheet without it, the
  `Paint` equals the stored screenshot, the address bar shows the kernel's
  URL, and a click navigates.
- **Hostile pages**, each through a real sandboxed renderer, with the memory
  bound and a stated time limit checked: CSS bombs (a 64 MiB sheet, `{` nested
  a million deep, a million rules, a 100,000-compound selector, `:is(` nested
  10,000 deep, 10,000 rules over 100,000 elements, timed against 5.5's bound);
  a font with malicious tables (offsets past the end, overlapping tables,
  `loca` not monotone, a composite glyph that contains itself, 32,767
  contours, overlapping `cmap` format 4 segments, `numGlyphs` disagreeing with
  `loca`), loaded as a test font; a million-element page, nested and flat; a
  million-column table and `colspan=1000` everywhere; `font-size: 1e9px`,
  `width: 1e9px`, margins of `-1e9px`; a page that tries to draw over the
  address bar (negative margins; an adversarial renderer sending a surface
  larger than the viewport, refused; a title shaped like a URL, shown only in
  the title bar); rows with no header or more rows than announced (the
  renderer is killed).
- **Phases 2 to 4 kept:** the demo, the escape attempts, the WPT `cookies/`
  rows, `pages.rs` (as box tree dumps, 5.0(g)) and `hostile_pages.rs` pass
  with the new schema.

### 5.27 Status and README (S)

`cargo xtask report --write` for the local preview; the Phase 5 note in
README.md (what `browse` does, the CSS subset, fonts, the platforms, the
memory bound, the new `unsafe` count); this file's Status table and exit
criteria one by one; ROADMAP.md; VERIFICATION.md's TCB list (the windowing
bindings, the compositor, the system font files; `clazel-text` removed and
`clazel-layout`, `clazel-window` added to the Tier 0 code on a page's path);
delete `clazel-text` per 5.0(g).

## Order of work

```
5.0 decisions (a) to (i)
5.1 data ─┬─> 5.2 tokenizer ─> 5.3 parser ─> 5.4 evidence ─┬─> 5.5 selectors ─────────────┐
          │                                                └─> 5.6 values ─> 5.8 sources ─┴─> 5.7 cascade ──┐
          ├─> 5.9 font tables ─> 5.10 outlines, matching ─> 5.11 shaping ───────────────────────────────────┤
          └─> 5.12 white space, line breaking ──────────────────────────────────────────────────────────────┤
5.13 boxes ─> 5.14 block, inline ─> 5.15 tables ─> 5.16 paint ──────────────────────────────────────────────┤
5.17 raster ────────────────────────────────────────────────────────────────────────────────────────────────┤
5.18 IPC + kernel: surfaces, viewports, input ─> 5.19 style sheet fetches ──────────────────────────────────┴─> 5.20 pipeline ─┐
5.21 macOS window ─┬─> 5.23 browse with a window ─────────────────────────────────────────────────────────────────────────────┴─> 5.25 harness ─> 5.26 demo ─> 5.27
5.22 Linux window ─┘
Phase 3: TLS in the kernel (3.5b, 3.5e to 3.5g, 3.7) ─> the https:// step of 5.26
5.24 iframe design: any time
```

5.1, 5.2, 5.9, 5.12, 5.13 (against a hand-built computed-style table), 5.17
(with 5.10's outline type), 5.18, 5.21, 5.22 and 5.24 start at once. 5.13 to
5.16 take computed style as a parameter (a table of the subset's computed
values per node), so layout does not wait for the cascade's proofs, as
Phase 4's tree builder took `TokFns`. The demo (5.26) needs the conformance
tests of 5.4, 5.5 and 5.7, not their proofs or tiers.

## Status

| Item | State |
|------|-------|
| 5.0 Decisions | to decide |
| 5.1 Inventory and test data | not started |
| 5.2 CSS tokenizer | not started |
| 5.3 CSS parser | not started |
| 5.4 CSS syntax evidence | not started |
| 5.5 Selectors | not started |
| 5.6 Property values | not started |
| 5.7 Cascade and computed values | not started |
| 5.8 Style sources and media queries | not started |
| 5.9 Font tables | not started |
| 5.10 Outlines and font matching | not started |
| 5.11 Shaping | not started |
| 5.12 White space and line breaking | not started |
| 5.13 Box tree | not started |
| 5.14 Block and inline layout | not started |
| 5.15 Table layout | not started |
| 5.16 Paint | not started |
| 5.17 Raster | not started |
| 5.18 IPC and kernel: surfaces, viewports, input | not started |
| 5.19 Kernel: style sheet fetches | not started |
| 5.20 Renderer pipeline | not started |
| 5.21 Window on macOS | not started |
| 5.22 Window on Linux | not started |
| 5.23 `clazel browse` with a window | not started |
| 5.24 Nested browsing contexts: design | not started |
| 5.25 Reference rendering harness | not started |
| 5.26 Exit demo, hostile pages, process tests | not started |
| 5.27 Status and README | not started |

**Phase 5: planned (2026-10-31); decisions in item 5.0 pending.**

## Risks

The three biggest first.

- **Text shaping and fonts.** Text is most of what HN draws, and engines
  differ most there: metrics (`hhea` against `OS/2` typo metrics), kerning,
  quirks-mode line height and anti-aliasing each move glyphs by a pixel, which
  moves line breaks and then table columns. Fonts differ by OS too (Verdana on
  macOS, measured; usually absent on Linux, where DejaVu Sans is wider).
  Mitigation: 5.25 compares geometry, not pixels, with the reference engine
  using the same font files; tests use the bundled font (5.0(c)); the
  `ttf-parser` and `rustybuzz` differentials pin advances and kerning exactly;
  the tolerance is set once, never loosened.
- **The breadth of CSS a real page needs.** One page already needs quirks
  mode, presentational hints, the auto table layout (non-normative in CSS
  2.1†, so CSS Tables 3's draft is followed), media queries and negative
  margins; other sites need floats and positioning at once. Mitigation: the
  subset is measured (5.1) and stated in the README, "parsed, no effect"
  properties are listed so a later phase adds only effects, and 5.0(b)'s
  option B is the named next step.
- **The window bindings widen the audited surface.** The window is the first
  code outside the sandbox that draws, and on macOS it needs `objc_msgSend`,
  one symbol called with many signatures, where a wrong signature is undefined
  behaviour Miri cannot see (it runs no foreign call). Mitigation: 5.0(e)'s W1
  keeps every call under `clazel-sys`'s one-call-per-block rule and an
  independent audit, each signature checked against Apple's header; no Rust
  callbacks or classes; no `unsafe` at all on Linux; no GPU (5.0(d)); the
  README states the new count.
- **Phase 3's TLS** (3.5b, 3.5e to 3.5g, 3.7). If it is late, Phase 5 is built
  but exit criterion 3 stays open, and the Status says so (5.0(f)).
- **The Miri budget.** Phase 4 ended with Miri over its 360-minute limit
  (phase-4.md, Status; PR #75). This phase adds seven suites, a rasterizer
  whose tests touch every pixel and layout tests on large documents.
  Mitigation: a stated stride per suite, 64×64 surfaces under Miri, a stride
  of fonts, system fonts ignored under Miri (they open files), and the 300 s
  guard, answered by restriding, not by ignoring.
- **Three tier-2 crates change at once** (5.18, 5.19). As 4.12, each lands as
  one pull request with proofs, mutations and process tests green.
- **Pixels through the kernel** may make scrolling slow; measured in 5.26,
  with shared memory a later, separately audited decision.
- **Copyright of the exit page.** Only counts are stored (5.1), CI uses our
  own fixture (5.26), and real-site screenshots stay local unless the
  maintainer decides otherwise.
- **Section numbers.** Many CSS numbers here are marked † and must be checked
  at the pinned text; CSS Syntax 3 and Selectors 4 are living drafts
  renumbered since their last Candidate Recommendations.
