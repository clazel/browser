# Phase 5: CSS, layout, graphics (the Show HN milestone), detailed plan

**Goal:** the renderer draws the page instead of describing it. The style
sheets a document names are parsed inside the sandbox (CSS Syntax Level 3),
their selectors are matched against the DOM arena Phase 4 built (Selectors
Level 4), the cascade gives every element its computed style (CSS Cascade
Level 4, with HTML §15's user agent style sheet and presentational hints),
the boxes are laid out as blocks, lines and tables (CSS 2.1 §9, §10, §17,
CSS Text Level 3), the text is set in fonts read from OpenType files, and a
rasterizer of our own turns the result into pixels. The host gains a native
window on macOS and Linux, with an address bar the renderer cannot draw
on. The kernel keeps its two display theorems in a new shape: a renderer's
pixels are shown only in its own tab, under the URL the kernel committed
there, and never outside the viewport the host gave it.

*Exit:* `cargo run -p clazel -- browse https://news.ycombinator.com/` opens
a window that shows the Hacker News front page laid out as a reference
browser lays it out, and the Show HN post's item page with its comment tree
can be read in it, with every parser on that path at its target tier.

Nothing in this phase decodes an image, submits a form or runs a script.
Images are Phase 6: an `img` is a box of the size its attributes give, drawn
empty, which is what Hacker News' spacer images need for the comment tree's
indentation. Forms are Phase 6: an `input` or a `textarea` is an empty
bordered box. JavaScript is Phase 7: `hn.js` is never fetched, so comments
cannot be collapsed and votes cannot be cast. Floats, positioning, flexbox,
grid, transforms, `@font-face`, bidirectional text and complex-script
shaping are not needed by the exit page (see "What the exit page needs")
and are Phase 8's CSS breadth unless 5.0(b) widens the subset.

A convention for this file: a section number marked † was written from the
documents as remembered, not read at a pinned commit, and must be checked
against the commit a spec header pins before it is cited there (SPEC-STYLE.md,
"Pin the source"). Numbers without the mark were read for this plan or are
already cited in the code.

## Exit criteria

Phase 5 is done when all of these hold on macOS arm64 and Linux x86-64:

1. The new crates are at their target tiers as 5.0 decides them, accepted by
   `cargo xtask check`. As recommended: `clazel-css` (CSS Syntax 3) and
   `clazel-selectors` (Selectors 4) at **tier 2** (every mutation a
   certified `killed`, conformance tests, an independent transcription
   each); `clazel-style`, `clazel-font` and `clazel-raster` at **tier 1**
   (Kani harnesses over all inputs up to a stated bound); `clazel-layout`,
   `clazel-window`, `clazel-renderer` and `clazel` at tier 0 with the
   evidence named in their items. `clazel-ipc` and `clazel-kernel` stay at
   tier 2 with the schema and theorems of 5.18 and 5.19.
2. The conformance suites run through the shipped code, vendored at pinned
   upstream commits, each printing its `clazel-conformance:` line
   (`xtask/src/conformance.rs`) and every expected failure listed by name
   with its reason:
   - CSS syntax: Servo's `css-parsing-tests` (the JSON files of
     `rust-cssparser`'s `src/css-parsing-tests/`) and the cases a converter
     extracts from WPT `css/css-syntax/`, plus a differential against
     Servo's `cssparser` crate (5.4);
   - selectors: the cases a converter extracts from WPT `css/selectors/`
     (parsing and serialization), the WPT `css/selectors/` reftests through
     5.25's harness, and a differential against Servo's `selectors` crate
     on random selectors and documents (5.5);
   - style: WPT `css/css-cascade/` and `css/CSS2/cascade/`† reftests, and
     the property-value parsing cases extracted from WPT `css/css-color/`,
     `css/css-values/` and `css/css-fonts/` parsing tests for the
     properties of the subset (5.6, 5.7);
   - fonts: a differential against `ttf-parser` and `read-fonts` (test-only
     dependencies) on every vendored font, every system font present on
     the runner and mutated fonts, with the OpenType specification's own
     worked examples evaluated as unit tests (5.9, 5.10); kerning against
     `rustybuzz` on Latin text (5.11);
   - text: the Unicode `LineBreakTest.txt` for UAX #14 (5.12);
   - layout and paint: a stated list of WPT `css/CSS2/` reftests
     (`normal-flow`, `margin-padding-clear`, `box-display`, `linebox`,
     `tables`, `text`, `colors`, `fonts`†) and `css/css-tables/`,
     `css/css-text/white-space/`, `quirks/` reftests through 5.25's
     harness, both pages of each reftest rendered by our own engine and
     compared pixel for pixel (with WPT's `fuzzy` annotations honoured and
     nothing else tolerated).
3. **Demo.** `cargo run -p clazel -- browse URL` opens a window with an
   address bar the host draws, the page below it, scrolling by wheel and
   keys, and links followed by a click. On
   `https://news.ycombinator.com/` and a Show HN item page, run locally
   (no Internet in CI): every story, its rank, title, site, score, user,
   age and comment count, and every comment with its indentation, are
   readable; the boxes of the page's text runs are within the tolerance
   stated in 5.25 of a recorded reference engine's boxes, and the pixel
   difference against that engine's screenshot is measured and reported
   (not asserted). In CI, the same checks run against an in-process server
   serving 5.26's HN-shaped fixture, with our own rendering stored as the
   reference screenshot and compared exactly. Until Phase 3's TLS is wired
   into the kernel (5.0(f)), the demo runs on `http://` sites and the
   in-process server, and this criterion says so.
4. `clazel-kernel` proves the display theorems restated over the new
   messages (5.18): `theorem_paint_only_own_tab`,
   `theorem_address_bar_integrity` (the URL shown with a renderer's pixels
   is the kernel's committed URL for its tab, whatever the renderer sends),
   `theorem_paint_fits_viewport` (no `Paint` is larger than the viewport
   the host set for that tab), `theorem_paint_is_the_surface` and
   `theorem_input_only_to_own_tab`; and over the style sheet fetches
   (5.19), `theorem_subfetch_only_to_requester` and
   `theorem_subfetch_credentials`. The Phase 2, 3 and 4 theorems still
   hold, restated over the new events and outputs.
5. The hostile pages of 5.26 (a CSS bomb, a font with malicious tables, a
   million-element page, a page that tries to draw over the address bar,
   and the others listed there) never panic a renderer, never exceed the
   renderer's stated memory bound, never take longer than the stated time,
   and never change what the host draws outside the content area.
6. Miri: every new `tests/conformance*.rs` runs a stated stride of its
   cases under Miri (`if cfg!(miri) { N } else { 1 }`, with the reason, per
   VERIFICATION.md "Tools"), sized to about a minute; no test takes 300 s
   or more of Miri's time; the Miri job finishes inside its CI limit.
7. `scripts/verify.sh` exits 0 and CI's full verification is green on the
   pull request that completes the phase; VERIFICATION.md's TCB list names
   the window and any GPU bindings, the OS compositor and the system font
   files; every change to `clazel-sys` has an audit row written by another
   session (CLAUDE.md rule 1).

## What is proven, and what is assumed

1. **Proven (Verus, tier 2, as 5.0(a) recommends):** the CSS Syntax 3
   tokenizer (§4) and parser (§5) as total functions from code points to
   tokens and from tokens to rules and declarations, with the two faces
   (whole input and one step) proven equal; Selectors 4 parsing, matching
   against the DOM arena and specificity; in the kernel, the paint, input
   and style sheet fetch theorems of 5.18 and 5.19; in `clazel-ipc`, the
   codec over the new messages.
2. **Proven absent of panics and overflow (Kani, tier 1):** the property
   value parsers, the cascade and computed values (`clazel-style`); the
   OpenType table parsers and glyph outline decoding (`clazel-font`); the
   rasterizer (`clazel-raster`). Each harness covers every input up to a
   stated bound (bytes of a table, tokens of a declaration, segments of a
   path, pixels of a surface); the bound is written in the harness and in
   the crate's README. Their correctness evidence is the conformance and
   differential tests, as Tier 1 allows.
3. **Small and tested, not proven (Tier 0, listed in VERIFICATION.md's
   TCB):** the layout (`clazel-layout`: box tree, block, inline and table
   layout, line breaking, hit testing, the display list), the renderer's
   pipeline glue, the host's window code (`clazel-window`) and its event
   loop. Layout and glue run inside the sandbox, so a bug can mis-render or
   kill one tab but not break a kernel theorem; their evidence is the
   reftests, the reference-rendering harness and the hostile pages.
4. **Assumed (TCB), new in this phase:** the OS windowing system and
   compositor (AppKit and the WindowServer on macOS; the X server, or
   XWayland and the Wayland compositor, on Linux), which put the host's
   pixels on the screen; the windowing bindings chosen in 5.0(e) (new
   foreign functions in `clazel-sys`, audited, or a shipped binding
   crate); GPU drivers only if 5.0(d) brings a GPU path in; the system
   font files the host reads by path (5.0(c)); the suites and engines the
   differential tests use, as evidence that the specs match the standards.

What a bug can and cannot do, stated once, as Phase 4 did: style, fonts,
layout and raster all run in the renderer, inside the sandbox, on bytes a
server chose. A bug there can draw the wrong pixels for its own tab or kill
it. It cannot draw outside its tab's content area, change the address bar,
or reach another tab, because the kernel checks the size of what it shows
(`theorem_paint_fits_viewport`), labels it itself
(`theorem_address_bar_integrity`), and the host draws the address bar in a
region no surface is placed in (5.23, tested by 5.26's hostile page). The
host's window code is outside the sandbox and is the one new place where a
bug matters to every tab; it reads no byte a page chose except the
surface's pixels, whose size the kernel has already checked.

Not covered by any theorem, and said so: that the page looks right (the
reftests and the reference harness are the evidence); timing and memory
beyond the stated bounds; `:visited` (never matches, so a page cannot
learn the history; listed in 5.5); `:hover` and `:active` (no hover state
in this phase); fonts beyond 5.0(c)'s scope (a character with no glyph in
any font is drawn as the `.notdef` box); right-to-left text (drawn in
logical order, listed); and the host's composition of chrome and content,
which is Tier 0 code with a test, not a theorem.

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-css` | 0 (2, per 5.0(a)) | CSS Syntax 3 §3 to §5, §8†; CSSOM "serialize" for tests | input decoding for style sheets, the tokenizer, the parser's entry points and algorithms, component values, An+B, serialization of tokens |
| `clazel-selectors` | 0 (2, per 5.0(a)) | Selectors 4 §3 to §7, §9, §15, §16, specificity, grammar† | parse a selector list, match against `clazel-dom`'s arena, specificity, serialization |
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
Phases 1 to 4. Syntax, selectors and style are three crates because a tier
is a property of a crate: the syntax crate's tier 2 must not wait for the
cascade, and the style crate's tier 1 must not be held to tier 2 by a
crate boundary. Font parsing and rasterization are separate because the
rasterizer also fills the boxes layout makes, and its harnesses are about
arithmetic, not bytes.

Section numbers are from the documents at the time of writing; each spec
header pins the exact commit or dated version it transcribes.

## Dependencies on Phases 3 and 4

**Phase 4** gives this phase its input and its display channel. Used as
they are: `clazel-dom`'s arena (parent, children, siblings, namespace,
local name, attributes, and the document's quirks mode, which the tree
builder sets in the "initial" insertion mode); `clazel-treebuilder`'s
`exec::driver::parse_real`; the renderer pipeline's content type, sniffing,
decoding and base URL steps (`crates/clazel-renderer/src/pipeline.rs`,
steps 1 to 4 of its module comment); `clazel-encoding`'s decoders (CSS
Syntax §3.2's "decode" uses Encoding §6 "decode", already proven); and the
commit protocol (`Commit`, `Body`, `BodyEnd`). Replaced: the text layout
(`clazel-text`, step 5 of the pipeline), the `Display` message (tag 10,
`crates/clazel-ipc/src/message/spec.rs`) and the kernel's `Show` output
(`crates/clazel-kernel/src/spec.rs`), and `browse`'s printing loop
(`crates/clazel/cli/browse.rs`). Phase 4's "Looking ahead" fixed the shapes
this phase builds on: selector matching reads the DOM through its readers;
computed style and the layout tree are side tables keyed by node id, not
fields of the DOM; `<style>` text and `style` attributes are kept as text
and attributes; a renderer's `Navigate` is how a click navigates.

**Phase 3** gives the network. The exit site is `https://` only
(`http://news.ycombinator.com/` answers `301` with `Location:
https://news.ycombinator.com/`, measured 2026-10-31). Phase 3's TLS is not
wired into the kernel's fetch: 3.5f's production libcrux and X.509 joins
are not started, 3.5g is not started, 3.5b's path validation is
unimplemented, and the host fails every `Connect` with `tls`
(phase-3.md, Status table, rows 3.5b, 3.5e, 3.5f, 3.5g and 3.7). That work
is a **prerequisite of the exit, and Phase 3's, not this phase's**
(5.0(f)); until it lands, every Phase 5 item is built and tested against
`http://` sites and the in-process server, and only the last step of the
demo waits.

## What the exit page needs

Measured on 2026-10-31 by fetching `https://news.ycombinator.com/` (34,653
bytes), its style sheet `news.css` (7,456 bytes) and one item page with 115
comments (164,969 bytes), and counting tags, attributes, inline styles,
selectors and properties. 5.1 repeats the measurement with a script, stores
the counts (not the pages) and keeps them current.

- **No `<!DOCTYPE>`:** both pages start `<html lang="en" op="news">`, so the
  document is in **quirks mode**, and the Quirks Mode Standard's CSS quirks
  apply (hashless hex colours and unitless lengths in the sheet's parsing,
  the line height calculation quirk, the table cell quirks), as does HTML
  §15.3.8's quirks-mode rule that tables do not inherit `font-size` and
  related properties, which is why `news.css` repeats its `body` rule for
  `td`.
- **Markup:** tables nested four deep for the whole layout (`<table
  id="hnmain" width="85%" bgcolor="#f6f6ef">`, `<td bgcolor="#ff6600">`),
  `center` (33 on the front page, 119 on the item page), `span`, `a`, `div`,
  `p`, `br`, `b`, `i`, `u`, `pre` and `code` in comments, `font size="1"`
  (116) and `font size="-2" color="#AFAFAF"`, a `form` with `input` and
  `textarea`, and `img`: the 18×18 logo (`y18.svg`) and spacer images
  `<img src="s.gif" height="1" width="40">` whose `width` (0, 40, 80, … in
  steps of 40) is the comment tree's indentation.
- **Presentational attributes** (HTML §15 presentational hints): `width`,
  `height`, `bgcolor`, `border`, `cellpadding`, `cellspacing`, `align`,
  `valign` (117 on the item page), `colspan`, `size` and `color` on `font`.
- **One external style sheet**, `<link rel="stylesheet" type="text/css"
  href="news.css?…">`, same-origin, so the renderer needs a style sheet
  fetch (5.19); inline `style` attributes (`height:5px` on 30 rows,
  `margin-top:2px; margin-bottom:-10px;` on 115 comment wrappers, `padding`,
  `text-align`, `line-height`, `display:block`, `border:1px white solid`);
  no `<style>` element.
- **Selectors in `news.css`:** type, class, ID, descendant combinator,
  compound selectors (`span.pagetop`, `table.padtab td`), attribute
  selectors (`input[type='submit']`, `input[readonly]`,
  `img[src='s.gif'][width='40']`), `:link`, `:visited`, `:hover`, and
  selector lists. No child, sibling or structural pseudo-classes.
- **Properties in `news.css` and the inline styles:** `font-family`
  (`Verdana, Geneva, sans-serif` and `monospace`), `font-size` (`pt`, `px`,
  `inherit`), `color` (hex), `background` and `background-color`,
  `text-decoration`, `margin` and its longhands (negative values included),
  `padding` and its longhands, `border` (shorthand, `0px`, `none`), `width`,
  `min-width`, `max-width`, `height`, `line-height` (`pt`, `px`,
  `normal`), `text-align`, `vertical-align`, `display` (`none`, `block`,
  `inline-block`), `visibility`, `overflow`, `white-space` (`pre-wrap`,
  `nowrap`), `overflow-wrap: anywhere`, `word-break: break-word`,
  `text-overflow`, `resize`, `cursor`, `pointer-events`, `transform`,
  `page-break-before`, `background-image`/`background-size` with `url()`
  and `linear-gradient()`, `!important`, and vendor-prefixed properties.
- **At-rules:** `@media only screen and (min-width: …) and (max-width:
  …)` (eleven of them, deciding comment widths by viewport) and `@media
  only screen and (-webkit-min-device-pixel-ratio: 2), only screen and
  (min-device-pixel-ratio: 2)`. No `@import`, `@font-face` or
  `@supports`.

What the exit therefore needs beyond a block-and-inline engine: the auto
table layout, quirks mode, presentational hints, media queries on width,
negative margins and margin collapsing, `overflow: hidden` clipping,
replaced boxes sized by attributes, and one fetch of a sub-resource. What
it does not need: floats, positioning, flexbox, grid, transforms (only on
the vote arrow, which can be drawn unrotated), images, `@font-face`.
The properties the subset parses but does not apply (`cursor`,
`pointer-events`, `resize`, `transform`, `page-break-before`,
`text-overflow`, background images) are listed in 5.6 as "parsed, no
effect", so that the cascade still sees them and a later phase only adds
their effect.

## Looking ahead: what Phases 6 to 8 will do with this

- **Images (Phase 6)** paint into replaced boxes 5.14 already sizes from
  attributes and CSS; a decoded image adds an intrinsic size and a pixel
  source to the display list's image item, which 5.16 defines and draws
  as nothing today. Background images likewise.
- **Forms (Phase 6)** replace 5.14's empty boxes for `input` and `textarea`
  with widgets; focus and keyboard input go through 5.18's `Input` message,
  which already carries keys.
- **JavaScript (Phase 7)** reads computed style (`getComputedStyle`) from
  `clazel-style`'s side table, mutates the DOM and asks for a restyle and a
  relayout. This phase computes style and layout for the whole document
  each time; the side tables are keyed by node id so that an incremental
  driver can recompute a subtree later without changing the proven
  functions. CSSOM needs serialization, which 5.4 and 5.5 build for the
  tests.
- **Web fonts** (`@font-face`) make font files page-controlled bytes. This
  phase's `clazel-font` is written for that from the start (Tier 1, hostile
  font tests), but loads only local fonts.
- **Nested browsing contexts** are designed in 5.24 and built later; an
  `iframe` is a box with its link, as in Phase 4.
- **CSS breadth (Phase 8):** floats, positioning, flexbox, grid,
  transforms, bidi, complex shaping, `@import`, `@supports`, and whatever
  WPT tracking shows next.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or
more. Each item follows CLAUDE.md rule 3 where its crate has a Tier 2
target: spec and contracts in one commit, then the implementation and
proof. Items in Tier 1 crates commit the Kani harnesses' statements first.
The decisions of 5.0 are pending; the items are written for the
recommendations and say where another choice changes them.

<!-- ITEMS -->

## Order of work

```
5.0 decisions (a)-(i)
5.1 inventory + test data ─┬─> 5.2 tokenizer ─> 5.3 parser ─> 5.4 syntax evidence ─┬─> 5.5 selectors ─┐
                           │                                                         └─> 5.6 values ─> 5.8 sources, media ─> 5.7 cascade ─┐
                           ├─> 5.9 font tables ─> 5.10 outlines + matching ─> 5.11 shaping ───────────┤                │
                           └─> 5.12 white space + line breaking ───────────────────────────────────────┤                │
5.17 raster (needs only 5.10's outline type) ───────────────────────────────────────────────────────────┤                │
5.13 box tree ─> 5.14 block + inline ─> 5.15 tables ─> 5.16 paint ─────────────────────────────────────┴────────────────┼─> 5.20 pipeline ─┐
5.18 IPC + kernel: surfaces, viewport, input ───────────────────────────────────────────────────────────────────────────┤                  │
5.19 kernel: style sheet fetches ────────────────────────────────────────────────────────────────────────────────────────┘                  │
5.21 macOS window ─┬─> 5.23 browse with a window ──────────────────────────────────────────────────────────────────────────────────────────┼─> 5.26 demo ─> 5.27
5.22 Linux window ─┘                                                                                                                       │
5.25 reference harness (with 5.16) ────────────────────────────────────────────────────────────────────────────────────────────────────────┘
5.24 iframe design (any time)
Phase 3: TLS in the kernel (3.5b, 3.5e to 3.5g, 3.7) ──> the https:// step of 5.26
```

5.1, 5.2, 5.9, 5.12, 5.13 (against a hand-built computed-style table),
5.17, 5.18, 5.21, 5.22 and 5.24 start at once. 5.13 to 5.16 take computed
style as a parameter (a table of the subset's computed values per node),
so layout does not wait for the cascade's proofs, as the tree builder took
`TokFns` in Phase 4. The demo (5.26) needs the conformance tests of 5.4,
5.5 and 5.7, not their proofs or tiers.

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

<!-- RISKS -->
