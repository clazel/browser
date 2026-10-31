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

### 5.1 Inventory and test data (M)

**Inventory.** A script under `scripts/` (run locally; no Internet in CI)
fetches the exit pages and the style sheets they link, and writes
`docs/phase5-inventory.md`: per page, the element, attribute and inline
style counts, and per style sheet, every selector shape, property, value
type, unit and at-rule, as "What the exit page needs" lists them. It stores
counts, never the pages or the sheet (whose copyright is Y Combinator's and
its users'). Rerun before 5.26, and any new property or selector shape is
added to 5.6's subset or listed as "not applied".

**Vendoring and conversion**, in the pattern of items 1.0, 3.3 and 4.1, each
with a `SOURCE.md` (URL, commit, SHA-256, licence) and a converter in
`xtask/src/testdata/` that reads the fixed format and fails if it changes:

- Servo's `css-parsing-tests` (the directory `src/css-parsing-tests/` of
  `servo/rust-cssparser`: `component_value_list.json`,
  `one_component_value.json`, `declaration_list.json`,
  `one_declaration.json`, `rule_list.json`, `one_rule.json`,
  `stylesheet.json`, `stylesheet_bytes.json`, `An+B.json`, `urange.json`,
  `color3*.json`) under `crates/clazel-css/tests/data/`. Its licence must
  be read when vendoring; if it does not permit redistribution, the
  converter's output (inputs and expected values) is not vendored either
  and the suite runs from a pinned download in `scripts/`, as Apple's
  mapping files were left out in 4.1. These files encode the expected
  output in their own JSON shape (`["ident", "foo"]`, `["function", name,
  …]`, `["error", "invalid"]`), which the converter maps to our token and
  rule types.
- WPT, at the commit the repository already pins (item 3.3): `css/css-syntax/`,
  `css/selectors/`, `css/css-cascade/`, `css/css-color/`, `css/css-values/`,
  `css/css-fonts/` (parsing tests only), `css/CSS2/` (the directories 5.25
  names), `css/css-tables/`, `css/css-text/white-space/`,
  `css/css-text/line-breaking/` and `quirks/`. Most `css-syntax` and
  selector parsing tests are testharness.js files that call a fixed set of
  helpers (`test_valid_value(property, value, serialized)`,
  `test_invalid_value`, `test_valid_selector`, `test_invalid_selector`,
  and the `css-syntax` tests' own); the converter extracts the literal
  arguments of those calls and refuses any file whose calls are not
  literals, which are counted as "not run" with the reason, never as
  passes. Reftests are vendored with their reference files and any
  `fuzzy` meta.
- Unicode: `LineBreak.txt`, `LineBreakTest.txt` and `EastAsianWidth.txt`
  (UAX #14 needs it for class resolution) at one pinned Unicode version,
  turned into tables by `cargo xtask tables` as `unicode.rs` already is.
- Fonts for the tests: the bundled font of 5.0(c) and a small set of
  open-licensed TrueType and OpenType files covering `cmap` formats 4 and
  12, composite glyphs, `kern` and `GPOS` pair kerning, a collection
  (`.ttc`) and a CFF font; each with its licence file.

Dev-dependencies for the differential tests (`cssparser`, `selectors`,
`ttf-parser`, `read-fonts`, `rustybuzz`) get `test` rows in
DEPENDENCIES.md with their exact versions, their dependency count measured
and the reason; if a chain is unreasonable, the fallback is 4.11's (a pinned
binary outside the workspace as a fixture).

### 5.2 CSS Syntax: input and tokenizer, spec and contracts (M)

`crates/clazel-css`, module `tokenizer/`. CSS Syntax Level 3 (pinned to
the dated Candidate Recommendation Draft or editor's draft commit the
header names): §3.2† "the input byte stream" (determine the fallback
encoding: the BOM, the protocol's `charset`, an `@charset "…";` rule as the
exact first bytes, the referring document's encoding, else UTF-8; then
Encoding §6 "decode" through `clazel-encoding`, already proven); §3.3†
"preprocessing the input stream" (CR LF, CR and FF to LF; U+0000 and
surrogates to U+FFFD); §4.1† the token types (`<ident-token>`,
`<function-token>`, `<at-keyword-token>`, `<hash-token>` with its type
flag, `<string-token>`, `<bad-string-token>`, `<url-token>`,
`<bad-url-token>`, `<delim-token>`, `<number-token>`, `<percentage-token>`,
`<dimension-token>` with their numeric value and type flag, unicode-range
if the pinned text still has it, `<whitespace-token>`, `<CDO-token>`,
`<CDC-token>`, colon, semicolon, comma, the brackets, EOF); §4.3† the
tokenizer algorithms, one spec function each, named as the standard names
them: "consume a token", "consume comments", "consume a numeric token",
"consume an ident-like token", "consume a string token", "consume a url
token", "consume an escaped code point", "check if two code points are a
valid escape", "check if three code points would start an ident sequence",
"check if three code points would start a number", "consume an ident
sequence", "consume a number", "convert a string to a number", "consume
the remnants of a bad url", each step numbered.

Modelling choices, listed in the header: the input is `Seq<u32>` after
preprocessing with "reconsume" as not advancing (as 4.6 did); numbers are
kept exactly, as the sign, integer digits, fraction digits and exponent the
standard's "convert a string to a number" reads, plus their value as a
rational (`int` numerator, power-of-ten denominator), never a float in the
spec (a float is computed from it once, in `clazel-style`, with the
rounding stated there); parse errors are not modelled (the standard
recovers the same way with or without them); the tokenizer has two faces,
`tokenize(input) -> Seq<Token>` and `next_token(state) -> (state, Token)`,
proven equal.

Proven about the spec, and seeded as mutations: `theorem_tokenizer_total`
(every call consumes at least one code point or emits EOF);
`theorem_tokens_bounded` (at most one token per code point, plus EOF, and
the code points a token carries come from the input or are U+FFFD);
`theorem_step_equals_whole`. Contracts: the exec `next_token` equals the
spec's; `tokenize` is its fold; no recursion in exec code.

### 5.3 CSS Syntax: the parser, spec and contracts (L)

`clazel-css`, module `parser/`. CSS Syntax §5† as one spec function per
algorithm with its steps numbered: the token stream (§5.3†: "consume a
token", "discard whitespace", "process", mark and restore as an index);
the entry points (§5.4†: "parse something according to a CSS grammar",
"parse a stylesheet", "parse a stylesheet's contents", "parse a block's
contents", "parse a rule", "parse a declaration", "parse a component
value", "parse a list of component values", "parse a comma-separated list
of component values"); and the algorithms (§5.5†: "consume a stylesheet's
contents", "consume an at-rule", "consume a qualified rule", "consume a
block", "consume a block's contents", "consume a declaration", "consume a
list of component values", "consume a component value", "consume a simple
block", "consume a function"), with "consume a declaration"'s `!important`
detection and its custom-property case, and the nested-rule handling the
pinned text has. The output types are the standard's: a style sheet is a
list of rules; a rule is an at-rule (name, prelude, optional block) or a
qualified rule (prelude, declarations, child rules); a declaration is a
name, a value as component values and an important flag. Also §6† "the
An+B microsyntax" (for `:nth-child`, 5.5) and §9† serialization of
component values ("serialization" as the tests compare it, which the
converter of 5.1 needs).

The CSS Syntax text was restructured in 2021 to 2024 for nesting (the
"consume a block's contents" algorithm and the mark and restore token
stream); the spec follows the pinned text, and the header lists where
`css-parsing-tests` (written against the 2014 text) expects the older
behaviour; those cases are expected failures with the reason, and the
`cssparser` differential lists the same differences.

Modelling choices: as 5.2; rules and declarations are trees of component
values bounded by the input (a lemma); "parse something according to a
CSS grammar" is a parameter (a grammar is a function from component values
to an option), so `clazel-selectors` and `clazel-style` call it with their
own grammars and the parser does not depend on them.

Proven: `theorem_parse_total`; `theorem_parse_bounded` (the total size of
the output's component values is at most the number of input tokens, so a
style sheet's parse is linear in its bytes); `theorem_blocks_balanced`
(each simple block's closing token is its opening token's mirror, or EOF).
The exec parser iterates with an explicit stack: nesting depth is a page's
choice (a CSS bomb is `{` repeated), and Verus proves no panics, not no
stack overflow.

### 5.4 CSS Syntax: implementation, independent transcription, conformance (L)

The exec tokenizer and parser over `&[u32]`, proven equal to the spec,
function by function, as `clazel-html`'s tokenizer was.

Independent (`independent.rs`): CSS 2.1 §4.1.1 "Tokenization" (the
tokenizer as a lexical grammar of regular expressions, a different text
and form) and §4.1.7 and Appendix G† (the core grammar and error recovery
rules of §4.2), transcribed without reading `spec.rs`, and proven equal
on the inputs where the two texts decide the same, with the differences
listed in the lemma (CSS 2.1 has no `<CDO>`/`<CDC>` handling in the same
places, different escape and `url(` rules, no nesting, and no numbers
with exponents), as `clazel-http` listed RFC 7230 against RFC 9112.

Conformance (`tests/conformance_syntax.rs`): every `css-parsing-tests`
file through the matching entry point, compared on the converted shape;
the WPT `css-syntax` cases 5.1 extracts; a differential against Servo's
`cssparser` (a `test` row) on random and mutated style sheets and on
every vendored sheet, comparing tokens and the rule structure, with the
places where `cssparser` follows the older text listed. Mutations: one or
more per tokenizer algorithm and per parser algorithm (a dropped case, an
escape not consumed, `!important` not detected, a block closed by the
wrong token), certified by example. Under Miri: the JSON suites in full if
they take under a minute, otherwise a stride, stated.

After 5.2 to 5.4: **raise `clazel-css` to tier 2** (if 5.0(a) chooses it).

### 5.5 Selectors: parsing, matching, specificity (L)

`crates/clazel-selectors`. Selectors Level 4 (pinned): the grammar†
(`<selector-list>`, `<complex-selector>`, `<compound-selector>`,
`<type-selector>`, `<attribute-selector>`, `<pseudo-class-selector>`,
`<pseudo-element-selector>` parsed and rejected for matching), parsed with
5.3's "parse something according to a CSS grammar" and the API hook
"parse a selector"†; elemental selectors (§5†: type, universal,
namespace prefix with the default namespace); attribute selectors (§6†:
`[a]`, `[a=v]`, `[a~=v]`, `[a|=v]`, `[a^=v]`, `[a$=v]`, `[a*=v]`, the `i`
and `s` flags, and class selectors as `[class~=v]`); ID selectors (§7†);
the location pseudo-classes `:link`, `:visited` and `:any-link` (§9†); the
tree-structural pseudo-classes `:root`, `:empty`, `:first-child`,
`:last-child`, `:only-child`, `:nth-child(An+B)` and their `-of-type`
forms (§15†); the logical combinations `:is()`, `:not()` and `:where()`
(§4†), but not `:has()`; the four combinators (§16†); "calculating a
selector's specificity" (§17†); and the API hook "match a selector against
an element"† over `clazel-dom`'s exec arena, read through its readers
only. Serialization (CSSOM "serialize a selector"†) for the WPT parsing
tests.

Modelling choices, listed: `:visited` never matches (no history is
exposed to a renderer, which also closes the history-sniffing channel the
standard's privacy note describes); `:hover`, `:active` and `:focus` never
match in this phase; pseudo-elements other than none parse and match
nothing (`::before` and `::after` generated content is not in the subset,
5.0(b)); in quirks mode, class and ID selectors match ASCII
case-insensitively (Selectors §6.6† and §7†, and the HTML standard's
quirks rules); HTML element and attribute names match as HTML's "case
sensitivity of selectors" says (lowercase for HTML elements in HTML
documents); `:has()` is out because matching it is not linear (listed,
Phase 8).

Proven: `theorem_parse_total`; `theorem_match_total` with a bound on work
(matching one complex selector against one element visits at most
`depth × compounds` ancestors and siblings, so a rule set's matching is
bounded by rules × elements × depth × compounds, which 5.26's CSS bomb
measures); `theorem_specificity_monotone` (adding a simple selector never
lowers specificity) and the standard's specificity examples evaluated;
`theorem_is_where_specificity` (`:where()` contributes zero, `:is()` its
most specific argument). Independent: CSS 2.1 §5† (the CSS 2.1 selector
syntax and matching, and §6.4.3 specificity) transcribed without reading
`spec.rs`, proven equal on the CSS 2.1 subset. Conformance
(`tests/conformance_selectors.rs`): WPT parsing cases extracted by 5.1;
WPT `css/selectors/` reftests through 5.25's harness (at the end of the
phase, when the pipeline draws); a differential against Servo's
`selectors` crate (with its `matching` over a small test DOM adapter) on
random selectors and random trees built by `clazel-treebuilder`.
Mutations per simple selector, per combinator, per specificity rule, and
for the quirks-mode case rule. Raise to tier 2 after the proof, the
transcription and the suites.

### 5.6 Property values for the subset (L)

`crates/clazel-style`, module `values/`. For each property of the subset
(5.0(b); as recommended, the properties "What the exit page needs" lists),
its value grammar from its defining specification, parsed with 5.3's
"parse something according to a CSS grammar": CSS Values 4 (`<length>`
with the absolute units `px`, `pt`, `pc`, `in`, `cm`, `mm`, `Q` and the
font-relative `em`, `ex`†, `rem`; `<percentage>`, `<number>`,
`<integer>`; the CSS-wide keywords `initial`, `inherit`, `unset`,
`revert`†); CSS Color 4 (hex notation in 3, 4, 6 and 8 digits, the named
colours table, `rgb()`/`rgba()`, `hsl()`/`hsla()`†, `transparent`,
`currentcolor`); CSS 2.1 and CSS Box 3 for `margin`, `padding`, `border-*`
(widths, `solid` and the other styles parsed, drawn as `solid`, listed),
`width`, `height`, `min-*`, `max-*`; CSS Display 3 for `display` (`none`,
`block`, `inline`, `inline-block`, `list-item`, `table` and its internal
values); CSS 2.1 §11 and CSS Overflow 3 for `overflow` and `visibility`;
CSS Fonts 3 §3† for `font-family`, `font-size` (keywords and the "legacy
font size" table HTML's `font size` maps to), `font-weight`, `font-style`
and the `font` shorthand; CSS 2.1 §10.8 and §16 and CSS Text 3 for
`line-height`, `vertical-align`, `text-align`, `text-decoration`†,
`white-space`, `overflow-wrap`, `word-break`, `text-indent`; CSS
Backgrounds 3 for `background-color` and the `background` shorthand's
colour (its images parsed, no effect); CSS 2.1 §17 for `border-spacing`,
`border-collapse`, `table-layout`, `caption-side`†; CSS Lists for
`list-style-type` (`disc`, `circle`, `square`, `decimal`, `none`).
Shorthands expand to their longhands as each specification's shorthand
definition says. "Parsed, no effect" properties are listed in the crate's
README; every other declaration is dropped as invalid, as Syntax says.

Quirks (Quirks Mode Standard §3.1† and §3.2†): in quirks mode, the
hashless hex colour quirk and the unitless length quirk apply to the
properties the standard lists.

Kani harnesses (tier 1): every value parser on every token sequence up to
a stated length (for instance 8 tokens with bounded payloads) returns
without panic or overflow; the numeric conversions (rational to fixed
point, unit to `px`) never overflow for any value, with out-of-range
values clamped to a stated range (lengths in 1/64 px as `i32`, a listed
modelling choice; CSS Values 4 allows clamping to an implementation range
and says so†). Conformance (`tests/conformance_values.rs`): the WPT
`css-color`, `css-values`, `css-fonts` and per-property parsing cases 5.1
extracts, for the properties of the subset, compared on their
serialization (CSSOM "serialize a CSS value"†); a property outside the
subset is counted as not run.

### 5.7 The cascade, inheritance and computed values (L)

`clazel-style`, module `cascade/`. CSS Cascade 4 (pinned): §6.1† cascade
sorting order (origin and importance, context, element-attached styles,
specificity, order of appearance; the encapsulation context is always the
document's, since there are no shadow trees); §6.2† the origins (user
agent, user: empty, author) and §6.3† important declarations; §6.4† and
CSS 2.1 §6.4.4 the precedence of non-CSS presentational hints (author
level, specificity zero, before every author rule); §4† value processing
(declared, cascaded, specified, computed; used values are layout's);
§7† defaulting (initial values, inheritance, `initial`, `inherit`,
`unset`, `revert`). The computed value of each property of the subset as
its definition table says (lengths to absolute `px`, `em` against the
parent's computed `font-size`, percentages kept where the property says
"as specified", `currentcolor` resolved for `color`).

The user agent style sheet is HTML §15's, transcribed into
`data/ua.css`† from the pinned HTML commit (§15.3.1 hidden elements,
§15.3.3 flow content, §15.3.4 phrasing content, §15.3.6 sections and
headings, §15.3.7 lists, §15.3.8 tables including its quirks-mode rules,
§15.3.10 form controls, §15.3.11 `hr`, and the parts of §15.4 that size
replaced elements), parsed by our own parser at build time and checked by
`cargo xtask tables` against the vendored text. Presentational hints are
the rules of §15.3 and §15.4 that map attributes to properties: `bgcolor`
and `color` through HTML's "rules for parsing a legacy colour value"
(§2.3.6†), `width` and `height` through "rules for parsing dimension
values" (§2.3.4.4†) and "maps to the dimension property", `align`,
`valign`, `border`, `cellpadding`, `cellspacing` (§15.3.8), `font size`
through "rules for parsing a legacy font size" (§15.3.4†), and `center`
and `align=center` centring block-level descendants (§15.3.3), which no
CSS property expresses and which is listed as a modelling choice with the
effect layout gives it. The output is a side table `computed: Vec<Style>`
indexed by node id, as Phase 4's "Looking ahead" fixed.

Kani harnesses (tier 1): the cascade's sort and the inheritance walk
never panic for any rule list and any tree up to a stated size; the walk
is iterative (a million nested elements, 5.26). Conformance: the WPT
`css-cascade` and `CSS2/cascade`† reftests through 5.25's harness, and a
golden table of computed values for the vendored HTML documents of 4.1
(every element's computed values for the subset, under the UA sheet only),
reviewed as fixtures. A Verus spec of the sort order (a total order and
its lemmas) is welcome and is what a later tier 2 would start from.

### 5.8 Style sources and media queries (M)

`clazel-style`, module `sources/`, and the renderer's use of it. What
style sheets a document has, in order, as HTML and CSSOM say: `<style>`
elements' child text ("update a `style` block", HTML §4.2.6†), `<link
rel=stylesheet>` elements' fetched sheets (HTML's link type "stylesheet"
and its "fetch and process the linked resource" steps†: in quirks mode a
same-origin sheet whose `Content-Type` is not `text/css` is still used,
otherwise it is not), and each element's `style` attribute (CSS Style
Attributes §3†: the value parsed as a block's contents, its declarations
in the element-attached context). The `media` attribute and `@media`
rules: Media Queries 4† for `all`, `screen` and `print` media types, `not`
and `only`, `and`, comma lists, and the `width`, `height`,
`min-`/`max-` forms and `orientation` features against the viewport; any
other feature is unknown and makes its query false (Media Queries 4's
rule for unknown features†), which is the effect `min-device-pixel-ratio`
and `-webkit-min-device-pixel-ratio` get (the second is defined by the
Compatibility Standard†, and HN's rule under it only changes a background
image's size, which this phase does not draw). `@import`, `@supports`,
`@font-face`, `@namespace` and `@page` are recognised and ignored, listed.

Kani: the media query evaluator on every query up to a bound. Tests: the
WPT `mediaqueries/` cases for the features above, extracted by 5.1; unit
tests per source.

### 5.9 Font file and table parsing (L)

`crates/clazel-font`. The OpenType specification (Microsoft, version
pinned in the header) chapters: "The OpenType font file" (the table
directory: `sfntVersion` `0x00010000` or `OTTO`, `numTables`, the table
records with tag, checksum, offset and length; the font collection header
`ttcf` and its offset table, since macOS ships `Helvetica.ttc` and
`Menlo.ttc`†); `head` (`unitsPerEm`, `indexToLocFormat`, the bounding box);
`hhea` (ascender, descender, line gap, `numberOfHMetrics`); `hmtx`
(advance widths and left side bearings, with the last advance repeated);
`maxp` (`numGlyphs`); `loca` (short and long offsets); `glyf` (simple
glyphs: contours, flags with their repeat and short-vector bits, x and y
deltas; composite glyphs: component flags, offsets or anchor points,
scale, x/y scale and 2×2 forms); `cmap` (the encoding records, preferring
Unicode full repertoire, and formats 4 and 12, with 0 and 6 if the
vendored fonts need them); `name` (family and subfamily names, IDs 1, 2,
16 and 17, in UTF-16BE); `OS/2` (`usWeightClass`, `fsSelection`, typo
metrics with `USE_TYPO_METRICS`, `sxHeight`); `post` (`isFixedPitch`,
underline position and thickness); the legacy `kern` table (version 0,
format 0); and `GPOS` LookupType 2 pair adjustment (formats 1 and 2) with
the Common Table Formats it needs (ScriptList, FeatureList for the `kern`
feature, LookupList, Coverage formats 1 and 2, ClassDef formats 1 and 2,
ValueRecord, and LookupType 9 extension). `CFF ` and `CFF2`, `GSUB`,
`gvar`/`fvar` (a variable font is read at its default instance), colour
tables (`COLR`, `CBDT`, `sbix`, `SVG `), bitmap tables and the TrueType
instructions (`fpgm`, `prep`, `cvt `, glyph instructions: hinting is not
done, so no bytecode interpreter runs on font bytes) are out unless
5.0(c) takes them; a font whose only outlines are CFF is not used.

Form: every table is parsed from a byte slice the directory gives, with
every offset and length checked against it (a table never reads outside
its own record's range, and the record's range is checked against the
file); parsing is lazy where a table is large (a glyph is decoded when
asked for) so a font is never expanded in memory beyond a stated bound.
Checksums are computed and a mismatch is recorded, not fatal (browsers do
not reject on it†, a listed choice).

Kani harnesses (tier 1): the directory and every table parser on every
byte string up to a stated length (and with symbolic offsets over a fixed
larger buffer, so that offsets near the end are covered); `loca` and
`glyf` together on symbolic glyph indices; no panic, no overflow, no read
outside the slice. Independent evidence (not a Tier 2 transcription,
since the target is 1): Apple's TrueType Reference Manual describes the
same tables from a different body, and the unit tests include its and the
OpenType chapters' worked examples. Differential
(`tests/conformance_fonts.rs`): `ttf-parser` and `read-fonts` on every
vendored font, every font found under the system font directories of the
runner, and 10,000 mutated fonts (bytes flipped, offsets moved, tables
truncated), comparing the directory, metrics, `cmap` lookups for every
code point the font maps, glyph outlines point by point and kerning pairs;
expected differences listed (for instance, where a library accepts a
table we reject).

### 5.10 Glyph outlines and font matching (M)

`clazel-font`, module `outline/`, and `clazel-layout`, module `fonts/`.
Outlines: a `glyf` glyph to contours of on-curve and off-curve points,
with the implied on-curve midpoints between consecutive off-curve points
made explicit, composite glyphs flattened with their transforms to a
stated nesting depth (a component cycle or depth beyond the bound is an
empty glyph, listed, for the hostile font of 5.26), scaled from font units
to pixels in fixed point (26.6, as FreeType's convention, a listed choice)
at the used font size. The outline type is `clazel-raster`'s path input, so
5.17 can start with it alone.

Font matching, in `clazel-layout`: CSS Fonts 3 §5.2† "matching font
styles" over the font table 5.0(c) gives (family name to faces with
weight, width and style), with the generic families `serif`,
`sans-serif` and `monospace` mapped per OS (5.0(c)); then per character,
§5.4†'s character handling: the first face in the `font-family` list
whose `cmap` maps the character, then the fallback list, then `.notdef`
of the first face. Kani: outline decoding on symbolic glyphs (5.9's
harness extended). Tests: outlines against `ttf-parser`'s; matching unit
tests per rule.

### 5.11 Shaping: characters to positioned glyphs (M)

`clazel-layout`, module `shape/`, over `clazel-font`. Scope per 5.0(c); as
recommended: a run of characters with one computed font to glyphs through
`cmap`, one glyph per character (no `GSUB`, so no ligatures; CSS Fonts'
default `font-variant-ligatures: normal` asks for `liga`, a listed
deviation), advances from `hmtx` scaled to the used size, kerning from
`GPOS` type 2 for the `kern` feature when the font has `GPOS` (Verdana on
macOS has `GPOS`, `GSUB`, `GDEF` and `kern`, measured 2026-10-31) and from
`kern` otherwise, and `letter-spacing` and `word-spacing` if 5.0(b) has
them. Combining marks are placed at the base's advance with zero advance
(no `mark` feature; listed). Right-to-left runs are drawn in logical
order (no UAX #9; listed, Phase 8). Positions are in 26.6 fixed point,
with no hinting.

Tests: a differential against `rustybuzz` (a `test` row) with the `kern`
feature only and `liga` off, on Latin, Greek and Cyrillic text in every
vendored and system font present: the glyph ids and advances must agree
exactly; expected differences listed. Unit tests: the OpenType chapters'
pair kerning examples.

### 5.12 White space and line breaking (M)

`clazel-layout`, module `text/`. CSS Text 3 (pinned): §3† the
`white-space` property and its values `normal`, `pre`, `nowrap`,
`pre-wrap`, `pre-line`; §4.1† phase I, collapsing and transformation
(segment breaks, collapsible spaces and tabs), and §4.2† phase II,
trimming and positioning at line starts and ends, hanging of preserved
spaces in `pre-wrap`; §5† line breaking and word boundaries with
`word-break` (`normal`, `break-all`, `keep-all`, and the legacy
`break-word` that HN uses, which CSS Text 3 defines as `normal` with
`overflow-wrap: anywhere`†) and §5.5† `overflow-wrap` (`normal`,
`break-word`, `anywhere`, which also affects min-content sizing and so the
table layout of 5.15). Line break opportunities from UAX #14 (pinned
Unicode version): the line breaking classes from `LineBreak.txt` with the
class resolution of LB1 (AI, SG, XX to AL; SA, CJ per the standard's
tailoring defaults), and the pair rules LB2 to LB31 in order, transcribed
rule by rule with the rule numbers in comments; mandatory breaks for
preserved segment breaks. `text-transform` is not in the subset.

Tests (`tests/conformance_linebreak.rs`): every line of
`LineBreakTest.txt` through the rules (passing / total, the standard's
tailorings that CSS asks for, if any, listed as expected differences);
the WPT `css-text/white-space/` and `css-text/line-breaking/` reftests
5.25 runs. Under Miri: a stride of the test file. The rules are a pure
function and small; a Kani harness over strings of a bounded length is
welcome.

### 5.13 The box tree (M)

`clazel-layout`, module `boxes/`. From the DOM and the computed style
table to a box tree in an arena, iteratively: CSS 2.1 §9.2† (block-level
and inline-level boxes, anonymous block boxes around inline content in a
block that also holds blocks, anonymous inline boxes), §9.7† (display,
position and float: positioning and floats are not in the subset, so
`position` and `float` compute and are ignored, listed), CSS Display 3's
`display: none` (no box) and `contents`† (out); list items (§12.5†, a
marker box with `list-style-type`); CSS 2.1 §17.2.1† anonymous table
objects (the three passes: remove irrelevant boxes, generate missing
child wrappers, generate missing parents), so that HN's `<tr
style='height:10px'/>` and stray text in tables produce the standard's
boxes; replaced elements (HTML §15.4†: `img` with its `width` and
`height`, sized and drawn empty, Phase 6; `input` and `textarea` as boxes
of the size HTML §15.5† suggests from `size`, `cols` and `rows`, drawn as
an empty bordered box; `iframe` as a box with its link, 5.24). Text nodes
become text runs after 5.12's phase I.

Input: computed style is a parameter (`StyleFns`: a function from node id
to the subset's computed values), so this item and 5.14 to 5.16 are built
and tested with hand-written tables before 5.7 lands. Tests: golden box
tree dumps for the html5lib tree-construction documents of 4.1 under the
UA sheet, reviewed as fixtures (this replaces `clazel-text`'s golden
test, 5.0(g)); and the anonymous-table WPT reftests.

### 5.14 Block and inline formatting (L)

`clazel-layout`, module `flow/`. CSS 2.1 §8.3.1 collapsing margins
(adjoining margins, negative margins, which HN's `margin-bottom:-10px`
needs, and clearance only as it arises with no floats); §9.4.1 block
formatting contexts (which `overflow` other than `visible` and
`inline-block` and table cells establish); §9.4.2 inline formatting
contexts and line boxes; §10.3.3† widths and margins of block-level
non-replaced elements in normal flow (the over-constrained rule), §10.3.2
and §10.3.4† replaced elements, §10.3.9† inline-block widths (shrink to
fit, §10.3.5†); §10.4 `min-width` and `max-width`; §10.6.3† and §10.6.7†
heights of blocks and of BFC roots; §10.5 and §10.7 `height`,
`min-height`, `max-height`; §10.8 line height calculations (the inline
box's leading, the strut, `vertical-align` values `baseline`, `top`,
`bottom`, `middle`, `sub`, `super`, `text-top`, `text-bottom` and
lengths), with the Quirks Mode Standard's line height calculation quirk
and blocks-ignore-line-height quirk (§3.3†, §3.4†) in quirks mode;
§16.1 `text-indent`, §16.2 `text-align` (`left`, `right`, `center`,
`justify` drawn as `left`, listed); the HTML `center` behaviour of 5.7;
the html-element-fills-viewport and body-element-fills-html quirks
(§3.6†, §3.7†). Line breaking at 5.12's opportunities, with the widths
5.11 measures. Overflow: content that does not fit is laid out
overflowing; `overflow: hidden` makes the paint clip (5.16).

Form: one pass that computes used widths top down and heights bottom up
over the arena with an explicit stack; every length in 1/64 px as `i32`
with saturating arithmetic (clippy's `arithmetic_side_effects` is denied
workspace-wide, so this is checked arithmetic by construction); the
result is a fragment tree (boxes with positions and sizes, line boxes
with positioned glyph runs) in a second arena keyed by box id, with a map
back to node ids for hit testing (5.18's clicks). The layout is redone
whole when the viewport width changes; nothing is incremental (Phase 7).

Tests: the WPT `CSS2/normal-flow`, `margin-padding-clear`, `box-display`,
`linebox`, `visudet`† and `visuren`† reftests through 5.25's harness, at
the pass count it reports; unit tests per rule; hostile layouts (5.26):
a million nested blocks, a line of a million characters with no break
opportunity, `width: 1e9px`.

### 5.15 Table layout (L)

`clazel-layout`, module `table/`. CSS 2.1 §17 (§17.2 the table model and
§17.2.1 anonymous objects from 5.13, §17.3† columns, §17.4† captions,
§17.5† the visual layout of table contents with §17.5.1† layers,
§17.5.2.1 the fixed table layout and §17.5.2.2 the automatic table
layout, §17.5.3 table height, §17.5.4 horizontal alignment, and
§17.6.1 the separated borders model; the collapsing borders model of
§17.6.2 if 5.0(b) takes it). The HTML table processing model† ("forming a
table": rows, cells, `colspan` clamped to 1000 and `rowspan` to 65534 as
HTML's `td` element says†, the cell grid with its slots) gives the grid.

CSS 2.1 says the automatic table layout algorithm it describes is
non-normative†, and real engines differ in it; HN depends on it entirely
(no table has `table-layout: fixed`). The spec followed is therefore CSS
Tables Level 3 (Editor's Draft, pinned to its commit)'s "computing column
measures" and "distributing width to columns"†, which describe what
engines converged on, with each step cited; where CSS Tables 3 is marked
unstable, the choice is listed and checked against the reference engine
of 5.25. The Quirks Mode Standard's table cell quirks (§3.8† height box
sizing, §3.9† width calculation, §3.10† nowrap minimum width) apply in
quirks mode. Percentage widths (`#hnmain` at 85%, HN's `width="100%"`
inner table), `min-width` on the table (`796px`), `cellpadding` as
padding on cells, `cellspacing` as `border-spacing`, `valign` as
`vertical-align` on cells (`top`, `middle`, `bottom`, `baseline`).

Tests: WPT `CSS2/tables` and `css-tables` reftests through 5.25's harness
(the latter mostly testharness.js layout tests that need JavaScript, so
only its reftests run; the count is reported); the HN-shaped fixture of
5.26 against the reference engine's geometry; hostile tables (5.26):
10,000 columns, `colspan=1000` in every cell, a million rows.

### 5.16 Paint: the display list (M)

`clazel-layout`, module `paint/`. From the fragment tree to a display
list: CSS 2.1 Appendix E.2† painting order, reduced to what the subset
creates (no positioned elements, no floats, no `z-index`: the root
stacking context only, so for each block in tree order its background and
borders, then its in-flow blocks, then its inline content: backgrounds,
borders, text, decorations), backgrounds (§14.2† `background-color`,
painted to the border box; the root and `body` background propagated to
the canvas as §14.2† says), borders (§8.5†, every style drawn as `solid`,
listed), text runs (positioned glyphs with a colour), `text-decoration`
lines (§16.3.1†: underline at the font's `post` underline position),
`overflow: hidden` clips (§11.1.1†, a clip rectangle), `visibility:
hidden` (painted nothing, still laid out), replaced boxes (nothing: the
image item exists for Phase 6), and hit regions (each link's fragments
with its resolved URL, for 5.18's clicks). The display list is a flat
list of items in paint order, each with integer device-pixel bounds, so
5.17 rasterizes only the items that intersect the viewport and a scroll
re-rasterizes without a relayout.

Tests: unit tests per item kind; the WPT `CSS2/colors`, `backgrounds`†
and `text` reftests through 5.25's harness.

### 5.17 Raster (L)

`crates/clazel-raster`, per 5.0(d); as recommended, a CPU rasterizer of our
own, target tier 1. Inputs: a surface size (width, height and a scale of 1
or 2 for HiDPI), a clip stack of integer rectangles, and items: fill a
rectangle with a colour; fill a path (closed contours of lines and
quadratic Béziers in 26.6 fixed point, which is exactly what `glyf`
outlines are) with a colour under the non-zero winding rule; draw a glyph
(a path, cached as a coverage mask per glyph, size and quarter-pixel
horizontal offset). Method: Béziers flattened to lines within a stated
tolerance (a quarter of a pixel), then exact-area coverage accumulation
per scanline (the signed-area method of `font-rs` and stb_truetype's
version 2 rasterizer, a stated choice), clamped to [0, 1], which equals
non-zero winding for contours that do not overlap with opposite
orientation (TrueType outlines may overlap; the difference is listed);
blending source-over in 8-bit sRGB with premultiplied alpha and no gamma
correction (listed). Output: RGBA8 premultiplied rows.

Kani harnesses (tier 1): for every path with at most a stated number of
segments and every coordinate in the 26.6 range `i32` allows, and every
surface up to a stated size, flattening and accumulation never panic,
overflow or index out of bounds, and every coverage is in [0, 255]; the
blend never overflows. Tests: unit tests per primitive; coverage of every
vendored font's glyphs at sizes 8 to 72 px compared against
`ab_glyph_rasterizer` or `tiny-skia` (a `test` row) within one level of
coverage per pixel, with the difference histogram reported; Miri on small
surfaces only (a 64×64 surface per test), stated in the tests.

A GPU path is not in this phase unless 5.0(d) decides otherwise.

### 5.18 The IPC schema and the kernel: surfaces, viewports and input (L)

`clazel-ipc`: the message schema changes (tags are never reused; `Display`
is retired and its tag 10 stays unused):

| Tag | Direction | Message | Fields |
|-----|-----------|---------|--------|
| 11 | renderer to kernel | `Surface` | title (text), width (unsigned), height (unsigned) |
| 12 | renderer to kernel | `SurfaceRows` | bytes (RGBA8 premultiplied rows, at most `max_body_chunk`) |
| 13 | renderer to kernel | `SurfaceEnd` | |
| 108 | kernel to renderer | `Viewport` | width, height (device pixels), scale (1 or 2) |
| 109 | kernel to renderer | `Input` | kind (unsigned: click, scroll, key), x, y (unsigned, in the content area), scroll delta as a sign (bool) and a magnitude (unsigned), since the CBOR profile has no major type 1 (`crates/clazel-ipc/src/cbor/spec.rs`), key (unsigned) |

`clazel-kernel`: per tab, a `viewport` (set by a new host event `Resize {
tab, width, height, scale }`, forwarded to the tab's renderer as
`Viewport`, and to every renderer the tab later spawns); per renderer, a
pending surface (the `Surface` header and the rows received so far, at
most `width × height × 4` bytes, checked as rows arrive). On `SurfaceEnd`
with exactly `width × height × 4` bytes, and `width` and `height` at most
the tab's viewport, the kernel outputs `Paint { tab, url, title, width,
height, pixels }` with `tab` and `url` from kernel state; anything else
(too large, too few rows, rows without a header, from an uncommitted
renderer) is a disallowed frame under item 2.10's rules. A new host event
`Input { tab, input }` becomes `ToRenderer` for that tab's renderer only.
`Show` is retired with `Display`.

Theorems, each with certified mutations: `theorem_paint_only_own_tab` (a
renderer's frames produce at most one `Paint`, for its own tab, and no
other output); `theorem_address_bar_integrity` restated (`Paint.url` is
the committed URL of the renderer the frames came from, for every message
content); `theorem_paint_fits_viewport` (`Paint.width` and `height` are at
most the tab's viewport, and `pixels.len() == width × height × 4`);
`theorem_paint_is_the_surface` (the pixels are the concatenation of the
renderer's `SurfaceRows` since its `Surface`, in order);
`theorem_input_only_to_own_tab` (an `Input` event for tab *t* produces at
most one output, a `ToRenderer` for *t*'s renderer); the Phase 2, 3 and 4
theorems restated with `Paint`, `Resize` and `Input` in the observations
(noninterference: a domain's `Paint`s agree between runs that agree on
the domain's events). Clicks: the renderer hit-tests (5.16's regions) and
sends the existing `Navigate`, which the kernel already treats as the
user's navigation (item 2.11); no new trust is needed. Scrolling: the
renderer keeps the scroll offset and re-rasterizes on `Input`; the kernel
does not see it.

The pixel path is the socket and the kernel's exec copy, which is simple
and proven; a 1280×800 surface at scale 1 is 4,096,000 bytes, four
frames. 5.26 measures repaint time; if it is too slow for scrolling, a
shared-memory surface (`memfd_create`/`mmap` on Linux, `shm_open`/`mmap`
on macOS: new `clazel-sys` calls, audited, and new sandbox rules) is a
later decision, not this item's.

### 5.19 The kernel: style sheet fetches (L)

Phase 4 left page-started fetches to later phases ("Looking ahead": new
IPC messages, the kernel's partition key choosing connections); HN's
`<link rel=stylesheet>` makes one necessary now (5.0(h)). `clazel-ipc`:

| Tag | Direction | Message | Fields |
|-----|-----------|---------|--------|
| 14 | renderer to kernel | `FetchStyle` | request (unsigned, the renderer's id for it), url (text) |
| 110 | kernel to renderer | `StyleResponse` | request, content type (bytes) |
| 111 | kernel to renderer | `StyleBody` | request, bytes |
| 112 | kernel to renderer | `StyleEnd` | request |
| 113 | kernel to renderer | `StyleFailed` | request |

`clazel-kernel`: a committed renderer's `FetchStyle` is resolved against
its committed URL; the request is Fetch's for a `<link rel=stylesheet>`
with no `crossorigin` attribute (destination "style", mode "no-cors"†),
run by the same 3.6 transducer the navigation uses, in a new
`Renderer::subfetches: Seq<SubFetch>` with at most a stated number at once
and per document, on connections owned by the tab with the renderer's
domain as partition key. **Credentials** (5.0(h)): a same-origin request
carries the jar's cookies and stores the response's `Set-Cookie`; a
cross-origin request omits both (Fetch would include them in "no-cors"
mode; the deviation keeps `theorem_cookie_noninterference`'s statement
unchanged and is listed). Redirects follow 3.6's rules; the final URL's
origin decides the credentials of each hop. The body goes to the
requester only, in `StyleBody` frames.

Theorems: `theorem_subfetch_only_to_requester` (every `Style*` output for a
request goes to the renderer that sent its `FetchStyle`, and only while
that renderer is committed to the same document); `theorem_subfetch_credentials`
(a `Send` of a sub-fetch carries jar-derived octets only if the request's
URL is same-origin with the renderer's lock; 3.6's `theorem_wire_cookies`
carried through); `theorem_connection_ownership` and the noninterference
theorem restated over sub-fetches. Mutations for each decision (credentials
on a cross-origin request, a response to another renderer, a sub-fetch
surviving a navigation, the limits). Tests: `tests/fetch.rs` cases for
each; through processes in 5.26.

### 5.20 The renderer pipeline (M)

`clazel-renderer`, `pipeline.rs` extended, Tier 0: after 4.13's steps 1 to
4 (content type, encodings, parse, base URL), collect the style sources in
tree order (5.8), send a `FetchStyle` for each `<link rel=stylesheet>`
whose `media` matches, and wait for all to end or fail (render-blocking,
as HTML says for style sheets in `head`†; a sheet that never answers is
failed by the kernel's timeout on `Tick`); decode each sheet (5.2's
§3.2), parse (5.3), cascade (5.7) into the computed table, build boxes
(5.13), lay out at the viewport width (5.14, 5.15), build the display
list (5.16), rasterize the viewport at the scroll offset (5.17), and send
`Surface`, `SurfaceRows`, `SurfaceEnd`. On `Viewport`: lay out again and
repaint. On `Input`: scroll (clamped to the page) and repaint, or
hit-test a click and send `Navigate`. `text/plain` documents become one
`pre` block styled by the UA sheet; other types show the notice, drawn.

Fonts: the renderer reads the font files of 5.0(c)'s table **before** it
enters the sandbox (the host passes the paths on the command line; the
Seatbelt profile and Landlock rules then forbid opening any file, as
today: `crates/clazel-sandbox/src/seatbelt.rs` and `syscalls.rs`), so no
sandbox rule is added for fonts. The memory bound of 4.13 is extended by
the style sheets (at most the body limit each, and the per-document
count), the computed table (one record per node), the box and fragment
arenas (a constant per node and per glyph), the display list and one
surface; stated in the crate README with its numbers and measured by
5.26. The renderer stays single-threaded (no `clone` in the seccomp
allowlist).

### 5.21 The window on macOS (L)

Per 5.0(e); as recommended, through `clazel-sys` in the audited style:
new foreign functions added to `xtask/src/sys.rs`'s list, each called in
one `unsafe` block with a `// SAFETY:` comment citing Apple's
documentation for the function, the checker extended to accept citations
of Apple's documentation (as `cites_win32_docs` accepts Microsoft's) and
to accept several `#[link_name = "objc_msgSend"]` declarations, one per
message signature, each listed by name. The calls: the Objective-C
runtime (`objc_getClass`, `sel_registerName`, `objc_msgSend` typed per
message) for `NSApplication` (`sharedApplication`,
`setActivationPolicy:`, `finishLaunching`,
`nextEventMatchingMask:untilDate:inMode:dequeue:` and `sendEvent:`, so the
event loop polls and no Objective-C class or callback is defined in
Rust), `NSWindow` (create, title, content view, close), and the view's
layer, whose `contents` is set to a `CGImage` made from the composed
pixels with Core Graphics' `CGColorSpaceCreateDeviceRGB`,
`CGDataProviderCreateWithData`, `CGImageCreate` and their releases;
`NSEvent` accessors for mouse location, button, scroll deltas, key codes
and characters. No policy lives in `clazel-sys`: `clazel-window` decides
what to open and what an event means.

Every change is audited by another session (CLAUDE.md rule 1); the author
leaves the audit step failing and says so in the pull request. The README's
`unsafe` count rises and is stated. Tests: a smoke test that opens and
closes a window (ignored under Miri and in CI jobs without a display,
with the reason), and unit tests of `clazel-window`'s event translation on
recorded events.

### 5.22 The window on Linux (L)

Per 5.0(e); as recommended, an X11 client of our own in safe Rust in
`clazel-window`, speaking the X Window System Protocol (X11R7, the
protocol document pinned) over a Unix socket (`/tmp/.X11-unix/X<n>` from
`DISPLAY`), so no `unsafe` and no shipped dependency is added: connection
setup with `MIT-MAGIC-COOKIE-1` from the `XAUTHORITY` file (its format is
parsed by us), `CreateWindow`, `ChangeProperty` for the title and
`WM_DELETE_WINDOW`, `MapWindow`, `CreateGC`, `PutImage` in `ZPixmap` format
(split to the server's maximum request length, with `BIG-REQUESTS` if the
server has it), and the events `Expose`, `ConfigureNotify`, `ButtonPress`
(buttons 4 and 5 are the wheel), `KeyPress` with `GetKeyboardMapping` for
keysyms, `ClientMessage`. Wayland sessions use XWayland; a native Wayland
client needs shared memory with descriptor passing, which `std` does not
offer in stable Rust, so it is Phase 8 (listed). The X server's replies
are parsed by our code at Tier 0 in the host: the server is part of the
TCB (it already sees every pixel), so the parser is tested, not proven;
the X protocol's encoding is fixed-size records, and every read is
bounds-checked by the workspace lints.

Tests: the protocol encoder and the reply parser against recorded
exchanges; a smoke test against `Xvfb` in CI's Linux job if the runner
image provides it (otherwise ignored with the reason).

### 5.23 `clazel browse` with a window (M)

`crates/clazel/cli/browse.rs` and `clazel-window`: open a window, a tab at
the URL, and loop on window events and kernel outputs. The window is two
regions the host composes: an address bar strip at the top, drawn by the
host from `Paint.url` (and an edit field when the user types a URL), and
the content area below it, where the latest `Paint` for the tab is
copied, clipped to the content area (its size is already at most the
viewport, 5.18). The host draws its own text (the address bar) with
`clazel-font`, `clazel-layout`'s shaping and `clazel-raster` on a bundled
or system font, outside the sandbox; it never draws a byte the page chose
in the strip. The page's title (from `Paint.title`) goes to the window's
title bar, after the URL, so that a title cannot look like the address.
Events: a resize sends `Resize`; a click or wheel in the content area
sends `Input` with coordinates relative to it; keys: typing in the
address bar and Enter navigate (`navigate_tab`), Escape cancels,
`Cmd/Ctrl-L` focuses it, `Cmd/Ctrl-[` goes back along the host's list of
committed URLs, `Cmd/Ctrl-R` reloads, Space, Page Up/Down and the arrows
scroll (sent as `Input`). The host shell (`crates/clazel/src`) gains only
the routing of `Paint`, `Resize` and `Input` and stays under 300 lines;
the window and the loop live in `clazel-window` and `cli/`.

`browse --headless OUT.png URL` (or a PPM, since PNG encoding is ours to
write and simple) renders one page to a file without a window: the
reference harness (5.25) and CI use it.

### 5.24 Nested browsing contexts: design (S)

Phase 4 left this design to Phase 5. A design note in this file (an
appendix), not code, recommended in 5.0(i): an `iframe` of another origin
is another renderer under the one-renderer, one-origin rule; the kernel
gains a frame tree per tab (each frame a renderer, its parent, and the
rectangle the parent's layout gave it, sent by the parent as a message);
the host composes the child's `Paint` into that rectangle, clipped, and
the kernel proves that a child's surface is placed only inside the
rectangle its parent assigned and that a parent never receives a child's
pixels or input. Same-origin iframes may share the parent's renderer.
What the theorems become (`theorem_paint_fits_viewport` per frame,
address bar integrity unchanged: the address is the top-level frame's)
and what it costs (a kernel state change as large as 5.18). Until it is
built, an `iframe` is a box showing its resolved URL as a link.

### 5.25 Reference rendering harness and reftests (M)

`crates/clazel/tests/reftests.rs` and `xtask`. **Reftests:** for each
vendored WPT reftest, render the test and its reference (`<link
rel=match>` or `mismatch`) with `browse --headless` at 800×600, scale 1,
with the bundled font for the generic families (so the result does not
depend on the runner's fonts), and compare pixel by pixel; a test's
`<meta name=fuzzy content=…>` gives its allowed maximum difference and
pixel count, and nothing else is tolerated. A reftest compares our engine
with itself on two equivalent pages, which is how WPT is designed and why
it is honest without a second engine. Tests that need JavaScript, images
or features outside the subset are counted as not run, by reason; the
pass count goes into the README table as a conformance row.

**Reference engine for the exit pages.** A script in `scripts/` (run
locally) loads a page in a pinned headless Chrome or Firefox at a fixed
viewport with the same fonts, and records (a) a screenshot and (b) every
text node's client rectangles and every element's border box (through
the browser's own `getClientRects`), as JSON with the browser's name,
version and the date. Our side dumps the same rectangles from the
fragment tree. The comparison is **geometry first**: every text run's
box within a stated tolerance (for instance 2 px in position and 2 % in
width, set once and never loosened to pass), with the number outside it
reported; the **pixel difference** of the screenshots is reported
(changed pixels and the mean difference), never asserted, because font
rasterization differs between engines by design. Our own screenshot of
the HN-shaped fixture is stored and compared exactly in CI, as a
regression test.

### 5.26 Exit demo, hostile pages, process tests (M)

- **Demo:** `cargo run -p clazel -- browse https://news.ycombinator.com/`
  on macOS arm64 and Linux x86-64 (X11 or XWayland), after Phase 3's TLS
  is in the kernel: the front page, a Show HN item page, a link followed
  by a click, scrolling, back; 5.25's geometry and pixel numbers recorded
  in the Status table. Before TLS: `http://` sites and the fixture.
- **The HN-shaped fixture:** a page and a style sheet written for this
  project (MIT, so they can be vendored and screenshotted), reproducing
  the measured shapes of 5.1 (quirks mode, the nested tables, the
  presentational attributes, the spacer images, the `font` elements, the
  inline styles, the selectors, properties and media queries), with
  invented text. The real pages and `news.css` are not vendored (their
  copyright is Y Combinator's and the commenters').
- **Through real processes:** an in-process server serves the fixture
  and its style sheet; a test drives `browse --headless` and the kernel:
  the sheet is fetched through `FetchStyle` with the page's cookie, a
  cross-origin sheet without it, the `Paint` is the stored screenshot,
  the address bar's URL is the kernel's, a click on a link navigates.
- **Hostile pages**, each through a real sandboxed renderer, with the
  renderer's memory bound and a stated time limit checked: a CSS bomb
  (a 64 MiB style sheet; `{` nested a million deep; a million rules; a
  selector of 100,000 compounds; `:is(` nested 10,000 deep; 10,000 rules ×
  100,000 elements, timed against 5.5's bound); a font with malicious
  tables (offsets past the end, overlapping tables, `loca` not monotone,
  a composite glyph that contains itself, `numberOfContours` of 32,767, a
  `cmap` format 4 with overlapping segments, `numGlyphs` disagreeing with
  `loca`), loaded through the font table as a vendored test font; a
  million-element page (nested and flat); a 1,000,000-column table and
  `colspan=1000` everywhere; `font-size: 1e9px`, `width: 1e9px`, negative
  margins of `-1e9px`; a page that tries to draw over the address bar
  (negative margins, a surface larger than the viewport from an
  adversarial renderer, a title that looks like a URL): the strip is
  unchanged and the oversized `Paint` is refused; a renderer that sends
  rows without a header or more rows than announced (killed).
- **Phase 2 to 4 kept:** the demo, the escape attempts, the WPT `cookies/`
  rows, `pages.rs` (converted from text to box tree dumps per 5.0(g)),
  `hostile_pages.rs` pass with the new schema.

### 5.27 Status and README (S)

`cargo xtask report --write` for the local preview; the Phase 5 note in
README.md (what `browse` does, the CSS subset, fonts, the platforms, the
memory bound, the new `unsafe` count); this file's Status table and exit
criteria one by one; ROADMAP.md; VERIFICATION.md's TCB list (the windowing
bindings, the compositor, the system font files; `clazel-text` removed
and `clazel-layout`, `clazel-window` added to the Tier 0 code on a page's
path); delete `clazel-text` per 5.0(g).

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
