# clazel-layout

Layout for [Clazel](../../README.md), a web browser whose parsers of untrusted
input carry machine-checked proofs (Phase 5, `docs/phases/phase-5.md`). So far:
font matching (item 5.10, `src/fonts/`), shaping (item 5.11, `src/shape/`),
white space and line breaking (item 5.12, `src/text/`), the box tree (item
5.13, `src/boxes/`), and block and inline formatting (item 5.14,
`src/flow/`). Table formatting and the display list (items 5.15 and 5.16)
are not started.

Its dependencies are `clazel-font`, which reads every byte of a font,
`clazel-style`, whose computed values the line breaker and the box tree read,
and `clazel-dom`, whose arena the box tree is built from. `rustybuzz` is a
dev-dependency, used only by the shaping differential, and `clazel-treebuilder`
one used by the box tree's and the formatting's tests to parse documents.

## Font matching (item 5.10)

CSS Fonts 3 §5.2 "matching font styles" over a given font table, with the
generic families mapped per OS (decision 5.0(c)), then §5.4's character
handling: the first face in the `font-family` list whose `cmap` maps the
character, then the fallback list, then `.notdef` of the first face.
`src/fonts/mod.rs` lists the modelling choices.

## Shaping (item 5.11)

`shape::Shaper` turns a run of characters in one face into glyphs:

1. each character to one glyph through the face's `cmap` subtable (an
   unmapped character is glyph 0);
2. its `hmtx` advance, or 0 for a combining mark;
3. pair kerning: `GPOS` LookupType 2 for the `kern` feature of the run's
   script, lookup by lookup in LookupList order, or else the `kern` table;
   a mark is skipped when pairs are formed.

The result is in font units (`UnitGlyph`: glyph, cluster, advance, offsets).
`shape::place` scales a run to 26.6 fixed point at the used size with item
5.10's scaling (`clazel_font::outline::scale::scale`), rounding each position
once, half away from zero, so rounding never accumulates along a run. No
hinting.

### Decisions taken for 5.11

Taken from the plan while the maintainer was away; each is also in
`src/shape/mod.rs`.

- **Scope is decision 5.0(c) H1**: `cmap`, `hmtx` and pair kerning, no
  `GSUB`, so no ligatures, though CSS Fonts' default
  `font-variant-ligatures: normal` asks for `liga` (a listed deviation).
- **No `letter-spacing` or `word-spacing`.** The plan includes them "if
  5.0(b) has them". Decision 5.0(b) A is what the exit page needs, and
  "What the exit page needs" lists neither property.
- **Kerning source.** The plan says `GPOS` when the font has `GPOS`, and `kern`
  otherwise. A face whose `GPOS` has no `kern` lookup in the chosen script
  table ("Script" below) is kerned from its `kern` table. That is the evident intent, and it is what HarfBuzz does. A `GPOS`
  that does not parse counts as absent. Only LookupType 2 is applied: a
  single adjustment that a font puts under `kern` is not (H1 is pair
  kerning; Euphemia UCAS on macOS has one).
- **Where a `GPOS` pair pass resumes**: after the second glyph when its value
  record is non-zero, else at it (HarfBuzz's reading: the chapter is silent;
  HarfBuzz tests `valueFormat2`, which `clazel-font` does not expose).
- **Marks**: a character in the combining-mark blocks of Latin, Greek and
  Cyrillic (U+0300–036F, U+0483–0489, U+1AB0–1AFF, U+1DC0–1DFF,
  U+20D0–20FF, U+2DE0–2DFF, Cyrillic Extended-B's marks, U+FE20–FE2F) has
  zero advance and is placed at the pen after its base. There is no `mark`
  feature, no `GDEF`, and kern pairs skip marks as if every lookup had
  `IGNORE_MARKS`.
- **The `kern` table's value goes to the first glyph's advance.**
  HarfBuzz splits it between the two glyphs instead, which puts every glyph
  in the same place.
- **Script**: the first character of the run in a Latin, Greek or Cyrillic
  block picks `latn`, `grek` or `cyrl`, else `DFLT`. The `GPOS` script
  table is the first one the font lists of that script, `DFLT`, `dflt` and
  `latn`. The first two are OpenType's rule (chapter2: use `DFLT` when the
  text's script has no table); `dflt` and `latn` are HarfBuzz's fallbacks
  for fonts that list neither, which make a run of punctuation in PT Sans
  kern as HarfBuzz kerns it. The chosen table decides even when it has no
  `kern` feature, and the `kern` table then applies. A listed table is the
  font's statement of which features its script gets, so going on to
  another script's `kern` would apply kerning the font did not ask for.
  This matches HarfBuzz: Liberation Serif Italic 2.1.5 (Ubuntu 24.04) lists
  `DFLT` with only `mark`, so digits are kerned from its `kern` table.
  `clazel-font` gained `Gpos::lists_script` for this.
- **Right-to-left runs stay in logical order** (no UAX #9, Phase 8). There is
  no Unicode normalization, no handling of default-ignorable characters and no
  space fallback.
- **Positions in 26.6**: a glyph's origin is its pen position plus its offset,
  scaled. Its advance is the difference of the scaled pen positions after and
  before it. A value outside `i32` is clamped. A negative size gives zeros.
- **Every failure degrades**, and nothing panics: an unreadable `cmap` gives
  glyph 0, an unreadable advance is 0, and an unreadable pair is not adjusted.
- **Target tier stays 0**, as the plan's Crates table gives for this crate.
  The shaper still has Kani harnesses for its arithmetic and indexing (below),
  as the item asked.

## White space and line breaking (item 5.12)

`src/text/`, against CSS Text 3 (W3C Candidate Recommendation Draft of
14 August 2026) and UAX #14 revision 57 (Unicode 18.0.0). An inline
formatting context's content (text items with their inline's
`white-space`, `word-break` and `overflow-wrap`, and atomic inlines) goes
through:

1. `collapse`: §4.1.1 Phase I, collapsing and transformation (with §4.1.3's
   segment breaks and §4's carriage returns and control characters), giving
   units: characters, collapsible or preserved spaces and tabs, other space
   separators, forced breaks and atomic inlines;
2. `wrap`: the line break possible after each unit (none, soft, forced, or
   an `overflow-wrap` emergency one), from UAX #14's rules with §3's
   `white-space`, §5.1's `word-break`, §5.4's `overflow-wrap` and §5.5's
   forced breaks and atomic inlines;
3. `lines`: §4.1.2 Phase II (leading and trailing removal, hanging,
   conditional hanging for `pre-wrap`, tab stops), first-fit line choice
   from the units' advances, and the min-content and max-content sizes.

UAX #14 is `classes` (LB1) and `uax14` (LB2 to LB31, rule by rule, in the
annex's order, each with its number and expression in a comment). The
character data are generated into `src/text/data.rs` by `cargo xtask tables`
(`xtask/src/linebreak.rs`) from Unicode 18.0.0's `LineBreak.txt`,
`EastAsianWidth.txt`, `emoji-data.txt` and `DerivedGeneralCategory.txt`,
vendored with their hashes under `data/unicode-18.0.0/`; `cargo xtask check`
fails if a file or the generated table drifts. Each file lists its modelling
choices at its top; `src/text/mod.rs` lists those that cross files.

### Decisions taken for 5.12

Taken from the plan while the maintainer was away; each is also in the
source.

- **The property types are `clazel-style`'s** computed `WhiteSpace`,
  `WordBreak` and `OverflowWrap` (item 5.7). The dependency points one way
  (`clazel-style` does not depend on layout), so no parameters were needed.
  `break-spaces`, which `clazel-style` parses, is implemented too.
- **Pinned texts.** CSS Text 3 at the CRD of 14 August 2026, the TR version
  when this was written; UAX #14 and its data at Unicode 18.0.0, the version
  `clazel-idna` already pins. The plan's section numbers carry † (written from
  memory): Phase II is §4.1.2 in the pinned text (the plan says §4.2),
  `word-break` §5.1 (plan §5.2†) and `overflow-wrap` §5.4 (plan §5.5†). The
  code cites the pinned numbers.
- **LB1's tailorings for CSS** (the plan's "SA, CJ per the standard's
  tailoring defaults"): CJ resolves to NS (LB1's default, CSS's `strict`;
  `line-break` is not in the subset, so it is `auto`). SA letters resolve to
  ID, not LB1's default AL, because CSS Text 3 §5.5 requires a soft wrap
  opportunity between letters of a script whose lexical analysis the UA
  cannot do (Thai, Lao, Khmer, Myanmar). Control characters of class CM
  resolve to AL (§4: treated as So). `LineBreakTest.txt` runs both with the
  default resolution (no expected differences) and with these tailorings
  (each difference explained by one of them).
- **No `line-break` or `hyphens`** (not in the subset), and §5.2's
  informative note on UAX #14 deviations is not applied.
- **Segment breaks always become spaces** (§4.1.3 leaves it UA-defined).
- **Collapsed spaces are removed**, rather than kept with zero advance.
- **Which box decides a break between two inlines**: after a space, the
  space's own style; otherwise wrapping needs both characters' `white-space`
  to allow it, and `word-break` and `overflow-wrap` are the earlier
  character's (§5.5 says this is undefined in this level).
- **`overflow-wrap` emergency opportunities** never split what UAX #14 keeps
  together by LB5, LB8a, LB9, LB26, LB30a or LB30b (an approximation of
  grapheme clusters, since there is no UAX #29 here), and are not added
  before a space or forced break.
- **Line choice is first fit**, with no prioritization of opportunities.
  Hanging and removed trailing white space is not measured for fit.
- **Tabs**: `tab-size` is not in the subset; its initial value is 8 spaces
  (`initial_tab_size`), and stops are measured from the pen the caller gives.
- **No bidi reordering** (Phase 8): line ends are logical ends.
- **Target tier stays 0**, as the plan's Crates table gives for this crate;
  the Kani harnesses below were added as the item welcomed them.
- **WPT reftests wait for item 5.25**: `css/css-text/white-space/` and
  `css/css-text/line-breaking/` are reftests, which need the rendering
  harness. They are not vendored or run here.

## The box tree (item 5.13)

`src/boxes/`, against CSS 2.1 (the Recommendation of 7 June 2011) §9.2, §9.7,
§12.5, §17.2.1 and §17.4, CSS Display 3† (`none`, `contents`), CSS Text 3's
Phase I (item 5.12), and HTML at commit `4c54fae1` §15.3.4, §15.3.7, §15.4 and
§15.5. `boxes::build(arena, styles)` takes the DOM arena and the computed
style, as `boxes::StyleFns` (a function from node id to `clazel-style`'s
`ComputedStyle`; item 5.7's `ComputedTable` implements it, and tests use
hand-written tables), and returns a `BoxTree`: an arena of boxes, each with
its kind, the node that generated it (`None` for an anonymous box), its parent
and its children, numbered in tree order. It runs, in order:

1. `generate`: each node's principal box and additional boxes (list items'
   markers), with text nodes as text runs, `display: none` generating nothing
   and `contents` hoisting its children; an iterative walk, one step per node;
2. `table`: §17.2.1's three stages (remove irrelevant boxes; generate missing
   child wrappers; generate missing parents), each rule by its number, then
   §17.4's table wrapper box (captions, then the table box);
3. `anonymous::split_blocks`: §9.2.1.1's anonymous block boxes, with an inline
   box that holds a block-level box split into fragments around it (first,
   middle and last, so borders can be opened as the section says);
4. `anonymous::text_runs`: Phase I (`text::collapse`) once per inline
   formatting context, and §9.2.2.1's removal of the white space it collapses
   away.

Every pass is a loop over a step whose state is small (`src/boxes/state.rs`
states each state's invariant), and none recurses: a document of 100,000
nested elements builds in under a second. Replaced elements (`img`, `input`,
`textarea`, `iframe`) are boxes with what HTML gives for their size; the
sizes that need a font (an `input`'s and a `textarea`'s character width and
height) are converted by layout (item 5.14). Each file lists its modelling
choices at its top; `src/boxes/mod.rs` lists those that cross files.

### Decisions taken for 5.13

Taken from the plan while the maintainer was away; each is also in the
source.

- **`StyleFns` returns `clazel-style`'s `ComputedStyle`** for a node id
  (`Option<&ComputedStyle>`), rather than a new type: the cascade is on
  `main`, its type already holds the subset's computed values, and a
  hand-written table is `ComputedStyle::initial()` with fields set.
- **§9.7 is the identity.** `position` and `float` are not in the subset
  (5.0(b) A): `clazel-style` neither parses nor computes them, so every box
  is in flow. The root element's blockification is the cascade's.
- **`display: contents`** is not a value the subset computes (item 5.6's list
  of `display` values does not have it, and the plan marks it "out"); it is
  implemented behind `StyleFns::display_contents`, which `ComputedTable`
  answers `false`, so hand-written tables can test it.
- **Replaced elements** are the four the plan names: `img`, `input`,
  `textarea` and `iframe`. An `img` is HTML §15.4.2's image that "represents
  nothing", with natural size 0 by 0 (no image is decoded in this phase), so
  its `width` and `height` come from its attributes through the
  presentational hints; its `alt` text is not shown. An `iframe` keeps its
  `src` for item 5.24. `audio`, `canvas`, `embed`, `object`, `video`, `button`
  and `select` are ordinary elements in this phase.
- **`br` and `wbr`** compute to `display: inline` (their `display-outside`
  values are not in the subset), so the box tree gives a `br` a text run of
  one line feed with `white-space: pre` (a forced break) and a `wbr` one of a
  zero width space (a soft wrap opportunity).
- **Lists.** Counters are not in the subset, so the `list-item` counter is
  computed here from what the user agent sheet and HTML's `start` and `value`
  hints would give it; `reversed` is not applied, and a list item outside its
  list's scope (after the list, CSS's following-sibling scope) counts in its
  own. `list-style-position` is not in the subset, so every marker is its list
  item's first child, placed as `outside`; HTML's quirks-mode `inside` for
  `li` is not applied. The predefined counter styles that are drawn are listed
  in `src/boxes/marker.rs`; every other one falls back to `decimal`.
- **§17.4's table wrapper box is built here**, so that table layout (item
  5.15) gets the captions apart from the table box. `caption-side` is not in
  the subset: every caption is above.
- **White space for §17.2.1** is CSS Text 3's document white space (spaces,
  tabs, line feeds, carriage returns), in any text run, whatever its
  `white-space`.
- **Order of the passes**: §17.2.1 before §9.2.1.1, Phase I last (see
  `src/boxes/mod.rs`).
- **What Phase I collapses away** is removed: a text run with no unit left,
  and every run of an inline formatting context that holds only collapsible
  spaces (Phase II removes those from the line's start). Other leading and
  trailing collapsible spaces stay for layout's Phase II. An anonymous block
  left with no children is removed; one holding only an empty fragment of a
  split inline is kept (a zero-height line), so no fragment is lost.
- **The plan's section numbers.** CSS 2.1's, marked † in the plan, were
  checked against the Recommendation's text; HTML §15.5's subsections were
  counted in the pinned source (§15.5.6 the text entry `input`, §15.5.17
  `textarea`). CSS Display 3, Lists 3 and Counter Styles 3 are cited with †.
- **Target tier stays 0**, as the plan's Crates table gives for this crate;
  the Kani harnesses below were added as the brief asked.
- **WPT anonymous-table tests wait for item 5.25**: they are reftests, which
  need the rendering harness. They are not vendored or run here.
- **The golden dumps are added beside `clazel-text`'s golden test**, which
  decision 5.0(g) G3 keeps until item 5.26; they replace it when that crate is
  deleted.

## Block and inline formatting (item 5.14)

`src/flow/`, against CSS 2.1 (the Recommendation of 7 June 2011) §8.3.1,
§9.4.1, §9.4.2, §10.1, §10.3.1 to §10.3.5, §10.3.9, §10.3.10, §10.4 to
§10.8.1, §16.1, §16.2 and §17.4; the Quirks Mode Standard (Living Standard of
19 October 2026, commit `5a06deb5`) §3.3 to §3.7; HTML at commit `4c54fae1`
§15.2's "align descendants", §15.4 and §15.5; and CSS Text 3 through item
5.12. `flow::layout(tree, arena, styles, fonts, viewport)` takes item 5.13's
box tree, the DOM arena (for the document's mode and replaced elements'
attributes), the computed style (`StyleFns`), the fonts (`flow::TextFns`)
and the viewport, and returns a `FragmentTree`: for every box laid out as a
box, its border box in document coordinates with its used margins, borders,
padding and baselines; every line box with its inline box pieces, positioned
glyph runs and atomic inlines; and the node each box came from. It runs:

1. `style.rs`: each box's style (anonymous boxes inherit; §17.4's split of a
   table's properties between its wrapper and table boxes);
2. `inline.rs`: each inline formatting context's units, wrap opportunities
   and shaped runs;
3. `intrinsic.rs`: min-content and max-content widths, leaves first;
4. `block.rs`: one walk with an explicit stack of tasks and a stack of
   block container frames: widths top down (`widths.rs`, `replaced.rs`), the
   block flow with margin collapsing (`margins.rs`), line boxes at each
   inline formatting context's end (`inline.rs`), heights bottom up
   (`heights.rs`), then every position made absolute.

`state.rs` states each state (a set of adjoining margins, a block
container's flow, the width equation's input and output, a line box's
extent, each box's role), its invariant as a function, and each step's
contract; it was committed before the implementation. Nothing recurses: a
tree 100,000 blocks deep lays out in 0.04 s (release). Each file lists its
modelling choices at its top; `src/flow/mod.rs` lists those that cross
files.

### Decisions taken for 5.14

Taken from the plan while the maintainer was away; each is also in the
source.

- **Fonts are a parameter** (`flow::TextFns`: an element's first available
  font's metrics, and a run's shaped glyphs), as computed style is for the
  box tree. `flow::FaceFonts` is the real one, over `clazel-font` faces with
  item 5.10's matching and item 5.11's shaper; `flow::BoxFont` gives every
  glyph an em square with the metrics of WPT's Ahem font, for tests whose
  geometry is worked out by hand.
- **A and D** (§10.8.1) are `OS/2`'s typo metrics when `USE_TYPO_METRICS` is
  set, else `hhea`'s, as engines read them; CSS 2.1's note recommends the
  typo metrics always (a note, listed). `line-height: normal` is A + D + the
  same table's line gap. An inline box's A and D are its first available
  font's, whatever face draws a glyph. The x-height is `OS/2`'s `sxHeight`, or
  half an em. `sub` lowers by a fifth of the parent's font size and `super`
  raises by a third (CSS 2.1 leaves both to the user agent). The leading's
  odd 1/64 px goes below.
- **Tables are item 5.15's; until then a placeholder**: the table wrapper is
  a block box with the table's margins and `width` (shrink-to-fit when
  `auto`), the table box a block filling it with the table's borders and
  padding, row groups, rows, cells and captions blocks in their parent's
  flow one below the other (cells and captions as block formatting context
  roots), and columns empty boxes. `border-spacing`, column widths, cell
  `vertical-align` and `colspan` have no effect yet. Every box in a table is
  laid out and its text readable.
- **Markers** (item 5.13: always `outside`) are a line of their own text in
  the list item's font, ending at its content edge, on its first baseline
  (or at its content top without one).
- **Inline boxes' edges** go before the box's first unit and after its last
  (for line breaking, with the unit beside them). An empty inline box takes
  no width and does not affect line heights, though CSS 2.1 §10.8 says empty
  inline boxes "still have margins, padding, borders and a line height"
  (listed). An edge beside a unit that Phase II removes at a line's end is
  dropped with it.
- **Default ignorable characters** (U+00AD, U+200B to U+200D, U+2060, U+FEFF),
  forced breaks and tabs draw no glyph (a font's `.notdef` would draw a
  box); a tab's advance is CSS Text 3 §4.2's.
- **A text run is shaped once, as a whole**: kerning between the last glyph
  of a line and the first of the next is applied as if they were adjacent.
- **A negative `auto` width is zero**, and the box is then over-constrained
  (`margin-right` follows from §10.3.3's equality).
- **HTML's "align descendants"** (`center`, `div align`, table parts'
  `align`, from `clazel-style`) is applied to a block-level box whose two
  horizontal margins are not `auto` and which rule 2 over-constrained with a
  greater `margin-right`, by the nearest aligning ancestor, unless the box
  aligns descendants itself (other than `center`); "set accordingly" is read
  as `auto` margins would place it. Table-internal boxes are never aligned
  (their margins do not apply).
- **`text-indent`**: a percentage is of the block container's own content
  width; CSS Text 3's `each-line` and `hanging` are applied; §16.1's
  anonymous-block rule is. `justify` is drawn as `left` (the plan), and a
  line too wide for its box is start-aligned (CSS Text 3 §7.1†).
- **The quirks**: §3.3 and §3.4 in quirks and limited-quirks mode, §3.5 to
  §3.7 in quirks mode. §3.3's "contains only collapsed whitespace" is read
  per line (collapsible spaces left by Phase I), and such a box is left out
  of the line's height rather than kept as a zero-height point. With §3.4's
  strut gone, the root inline box counts only on a line where it holds text
  of its own. §3.5's "UA-defined value" for a table cell is none (the
  percentage is `auto`). §3.7's parent content box is the `html` element's as
  §3.6 makes it at least (the viewport less its margins, borders and
  padding).
- **Replaced elements' natural sizes**: `img` 0 by 0, `iframe` none (300 by
  150), text `input` and `textarea` by HTML §15.5.6's character width
  conversion (the average character width is the advance of `0`:
  `clazel-font` does not read `xAvgCharWidth`) and the used line height,
  buttons by the width of their `value` (or "Submit", "Reset"), checkboxes
  and radio buttons 13px square. Their baseline is the bottom margin edge
  (CSS 2.1's rule); engines align a text control's text instead (listed).
- **Block formatting context roots**: the root element, inline blocks,
  table cells, captions, the placeholder's table boxes, and blocks whose
  `overflow` is not `visible` unless propagated to the viewport (the root
  element's always is; the `body`'s when the root's is `visible`).
- **CSS 2.1 §8.3.1's definition and bullets disagree**; the bullets are
  followed (`docs/ERRATA.md`, "Reported upstream: not yet").
- **A consequence to check against item 5.25's reference engine**: §8.3.1
  reads the *computed* `height`, so in quirks mode a last child's bottom
  margin still collapses through a `body` that §3.7 stretched; the
  html5lib case `<p>One<p>Two` gives an `html` box of 608px in a 600px
  viewport.
- **The plan's section numbers**: CSS 2.1's (marked †) were checked against
  the Recommendation; the Quirks Mode Standard's against the pinned text
  (they are the plan's). CSS Text 3 §7.1 is cited with †.
- **Target tier stays 0**, as the plan's Crates table gives for this crate;
  the Kani harnesses below were added as the brief asked.
- **WPT reftests wait for item 5.25**: `css/CSS2/normal-flow`,
  `margin-padding-clear`, `box-display`, `linebox`, `visudet` and `visuren`
  are reftests, which need the rendering harness. They are not vendored or
  run here.

### Not covered by 5.14

Floats, positioning and clearance (not in the subset); table layout (item
5.15; the placeholder above); `overflow` clipping and painting (item 5.16);
bidirectional reordering (Phase 8); `letter-spacing`, `word-spacing`,
justification, hyphenation; vertical writing modes; `box-sizing` (not in the
subset).

## Verification

Tier: `tier = 0`, `target-tier = 0` in `Cargo.toml` (the plan's Crates table).

Unit tests: `src/fonts/` per CSS Fonts rule; `src/shape/tests.rs` from the
`gpos` chapter's pair kerning examples (Example 4, PairPosFormat1 "Po"/"To";
Example 5, PairPosFormat2 lowercase before punctuation), each wrapped in a
minimal `GPOS` table and run through the kerning pass, plus the resume rule,
mark skipping and the `kern` table.

Kani harnesses (`src/shape/proofs.rs`) for the shaper's arithmetic and
indexing: no panic, no arithmetic overflow and no index out of bounds, on every
input within these bounds, with every loop's unwinding checked. Measured
locally, one harness at a time with `cargo kani -p clazel-layout --harness …
--exact`, on an Apple-silicon Mac while a Miri run used one other core. Times
are wall clock, including cargo's start. Memory is the peak resident set
size of the run, CBMC included.

| Harness | Inputs | Time | Peak memory |
|---------|--------|------|-------------|
| `pen_any` | the pen's accumulation and clamping on any pen (`i64`) and advance | 1.2 s | 0.15 GB |
| `to_26_6_any` | font units to 26.6 for any value, any size and any `unitsPerEm`; 0 for a negative size or zero `unitsPerEm`; the sign kept | 1.9 s | 0.16 GB |
| `place_step_any` | one glyph placed from any pen position, any glyph, any size and `unitsPerEm` (the body of `place`'s loop for every run length) | 5.8 s | 0.55 GB |
| `place_any_2` | whole runs of up to 2 glyphs, any values, any size and `unitsPerEm` | 23.4 s | 1.67 GB |
| `add_value_any` | any ValueRecord added to any glyph | 1.0 s | 0.15 GB |
| `next_base_any_6` | the next non-mark glyph after any index in any run of up to 6 glyphs is inside the run, after the index, and not a mark | 3.5 s | 0.20 GB |
| `kern_pass_any_4` | the `kern` table pass on any run of up to 4 glyphs with any value for every pair; it terminates | 9.0 s | 1.07 GB |
| `pair_pass_any_4` | the `GPOS` pair pass on any run of up to 4 glyphs with any answer (none, or any two ValueRecords) for every pair; it terminates | 29.9 s | 4.21 GB |

**Not covered by Kani**: reading the face (`cmap`, `hmtx`, `GPOS`, `kern`
are `clazel-font`'s, with that crate's harnesses; the passes here take the
pair lookups as arbitrary answers); `Shaper::glyphs`, which iterates a `&str`
and calls the face and has no arithmetic of its own; and runs longer than
the bounds above. Those are covered by the unit and differential tests.
CI has not run these harnesses yet.

`tests/conformance_shaping.rs` compares the shaper with `rustybuzz` 0.20.1
(HarfBuzz's algorithm in Rust). `rustybuzz` runs with the `kern` feature on and
every other feature it would apply turned off (`liga` among them), left to
right, at cluster level `Characters`, with the script our shaper chose. The
texts are Latin, Greek and Cyrillic sentences (including combining marks),
every ordered pair of characters from an alphabet per script, and every
triple from twelve Latin characters that kern: 22,830 texts per face. For
each glyph the test compares, in font units, the glyph id, the cluster and the
advance, and the offsets of every glyph that is not a mark.

| Suite | Cases | Agree | Expected differences | Failures |
|-------|-------|-------|----------------------|----------|
| vendored fonts (5 TrueType faces; the CFF face is skipped) | 114,150 | 114,147 | 3 | 0 |
| system fonts (this Mac: 406 files, 666 faces, every 11th case) | 1,382,253 | 1,361,817 | 20,436 | 0 |

The vendored expected differences are 2 `canonical composition` and 1
`unmapped character`. On the system fonts: 6,873 `unmapped character`, 6,800
`AAT tables`, 6,665 `kern table split`, 49 `GDEF mark classes`, 31
`canonical composition`, 15 `non-pair lookups under kern`, 3 `marks in kern
pairs`. The top of the test file explains each one. Under Miri the vendored
suite runs every 1,000th case: 115 cases, all agreeing, in 46 s on Miri's
clock. The system suite opens files, so it is ignored under Miri. Natively
the vendored suite takes 4 s and the system suite 65 s.

### White space and line breaking (item 5.12)

`tests/conformance_linebreak.rs` runs every line of Unicode 18.0.0's
`LineBreakTest.txt` (the file's own count, 19,346 lines, is checked) through
the rules:

| Suite | Lines | Pass | Expected differences | Failures |
|-------|-------|------|----------------------|----------|
| default rules (LB1's default resolution) | 19,346 | 19,346 | 0 | 0 |
| with CSS Text 3's tailorings (`Props::css`) | 19,346 | 19,209 | 137 | 0 |

The 137 expected differences are 75 `SA as ID` and 62 `control as So`, the
two tailorings of LB1 CSS asks for ("Decisions taken for 5.12"); the top of
the test explains each. Natively the test takes 0.2 s.

Unit tests (`src/text/tests.rs`): Phase I per step (spaces, tabs, segment
breaks, carriage returns, bidi controls, across inlines, each `white-space`
value), opportunities per property value (`white-space`, `word-break`,
`overflow-wrap`, forced breaks, atomic inlines, Thai), Phase II trimming and
hanging, CSS Text 3 §4.1.2's three `pre-wrap` examples (line contents and
conditional hanging as the text renders them), line choice with and without
`overflow-wrap`, min-content and max-content, and tab stops. Two more compare
the step formulations with `src/text/reference.rs`, the first readings (UAX
#14 looking through the whole text from each position; Phase I as five
passes): `uax14_step_matches_reference` on every string of 1 to 3 over an
alphabet of every class and the flag combinations the rules read, and on
200,000 random strings of 4 to 16 weighted towards long space, mark, RI and
number runs; `collapse_step_matches_reference` on every sequence of 1 to 4
over 30 (character kind, `white-space`) symbols and on 100,000 random ones of
5 to 24. Flipping the step's RI parity makes the first fail.

**Steps.** Each pass is a loop whose body is a step over a small state
(`src/text/state.rs`, which states each state's invariant as a function):

- UAX #14 (`uax14::step`) keeps the previous character's class, LB8's `ZW
  SP*`, the last two items, the last item before spaces with LB15a's start
  context, LB25's `NU ( SY | IS )*` and `… ( CL | CP )`, and LB30a's RI
  parity; the right context is the at most two items that LB15b, LB15c,
  LB19a, LB25 and LB28a read, passed as arguments. No rule needs more: every
  unbounded context in the rules is a regular expression the state follows.
- Phase I (`collapse::step`) keeps what the last unit kept was, a pending
  collapsible space that a later segment break retracts (step 1's
  "preceding"), and whether only spaces have come since the last segment
  break (step 1's "following").
- The CSS opportunity (`wrap::wrap_at`) reads only the two units around a
  position. Choosing lines (`lines::fit_step`) and measuring
  (`Measure::add`) step over the line being filled.

The restructuring changed no result: `LineBreakTest.txt` gave 19,346 /
19,346 (default) and 19,209 with 137 expected differences (CSS) before and
after, and every unit test passed unchanged.

Kani harnesses (`src/text/proofs.rs`). A **step harness** takes any state
satisfying the invariant and any next input, and checks no panic, overflow
or out-of-bounds index, the stated properties, and that the invariant is
kept; the start state satisfies it, so by induction the properties hold for
texts **of every length**. A **driver harness** runs a whole pass on bounded
inputs, as a cross-check that the driver calls its step correctly. Measured
locally, one harness at a time with `cargo kani -p clazel-layout --harness …
--exact`, each in its own process group capped at 20 minutes and 8 GB
(resident set of the whole group, polled every 5 s), on an Apple-silicon Mac.
Times are wall clock including cargo's start; memory is the larger of the
5 s samples and the largest child's `getrusage` peak.

| Harness | Kind | What it checks | Time | Peak memory |
|---------|------|----------------|------|-------------|
| `uax14_step_any` | step, every length | UAX #14 from any state, any character, any right context: LB2 at sot, LB4, LB7, LB9, mandatory breaks only after BK, CR, LF, NL; invariant kept | 8.5 s | 0.39 GB |
| `collapse_step_any` | step, every length | Phase I: at most one unit per character, only a pending space retracted, never a collapsible space right after another (bidi aside); invariant kept | 1.6 s | 0.19 GB |
| `wrap_at_any` | step, every length | CSS's opportunity: forced exactly where UAX #14 is mandatory or at the end; nothing soft or emergency where neither unit's `white-space` wraps | 1.9 s | 0.20 GB |
| `measure_add_any` | step, every length | measuring a line: saturating, leading spaces and forced breaks take no width | 1.4 s | 0.19 GB |
| `fit_step_any` | step, every length | choosing lines: a line ends after at least one unit and at most at the unit added; a line that goes on keeps the invariant | 2.0 s | 0.20 GB |
| `tab_advance_any` | any values | tab stops: never negative, at most two tab sizes, 0 for a size ≤ 0 | 1.5 s | 0.20 GB |
| `uax14_driver_matches_reference_2` | driver, bounded | `breaks_with_rules` equals `reference.rs`'s reading on any 2 characters' properties | 40.1 s | 1.10 GB |
| `intrinsic_any_3` | driver, bounded | min-content and max-content on any 3 units, opportunities and advances | 4.1 s | 0.35 GB |
| `trim_any_3` | bounded | Phase II on any 3 units and bounds: the reported ranges are ordered and inside the units | 2.8 s | 0.26 GB |

**Proved for every length**: `uax14::step` (and so `breaks_with_rules`'s
decisions, which are its outputs in order), `collapse::step`, `wrap::wrap_at`,
`Measure::add`, `lines::fit_step`, `lines::tab_advance`. **Only for bounded
inputs**: the drivers as whole loops (`uax14::breaks_with_rules` against the
reference on 2 characters; the intrinsic sizes on 3 units) and
`lines::trim`, which walks back from a line's end rather than stepping.

Capped, shrunk or removed on the way (none retried as it was). Before the
restructuring, bounded whole-string harnesses (2 to 4 characters) were the
only coverage: building inputs as a `Vec` put `trim_any_4`,
`break_lines_any_4` and `intrinsic_any_4` over 8 GB; `uax14_any_3` passed 8 GB
after 11 minutes and was split by position; `wraps_any_3` passed 8 GB; a
Phase I harness passed 8 GB at 4, 3 and 2 characters; and a `tab_advance`
with a division and a 64-bit product ran 10 minutes (rewritten with one
`rem_euclid`). After it, driver harnesses for Phase I (`collapse_driver_any_3`,
then `_any_2`) and for `break_lines` (`break_lines_any_3`, then `_any_2`)
passed 8 GB and were removed; their steps are proved for every length.
`collapse_step_any` first failed because the stated invariant was weaker than
what the driver keeps (it allowed a segment break as the last unit without
`after_break`); the invariant now states the equivalence.

**Not covered by Kani**: the character tables (bisection over thousands of
ranges; the harnesses take the properties as arbitrary values, and the
conformance test covers the tables); that each step computes exactly the
rules beyond the asserted properties (the equivalence tests and the bounded
driver harness compare it with the reference reading); the Phase I and
`break_lines` drivers as whole loops (above); and reading a `&str` into
units. CI has not run these harnesses yet.

Miri: every test this item adds, measured one test per process with
`cargo +nightly-2026-08-21 miri test -p clazel-layout … --exact -Z
unstable-options --report-time`, each capped at 10 minutes. Times are on
Miri's clock. Under Miri the conformance test runs 100 lines sampled at
evenly spaced byte offsets of the file (99 of them data lines), because
reading the whole 3 MB file line by line under Miri took over ten minutes
before any rule ran; the file's line count is checked natively only.

| Test | Miri time |
|------|-----------|
| `text::tests::collapse_step_matches_reference` (every 997th exhaustive sequence, 60 random) | 82.5 s |
| `text::tests::uax14_step_matches_reference` (every 997th exhaustive string, 60 random) | 46.8 s |
| `conformance_linebreak::line_break_test` (99 sampled lines, both suites) | 35.9 s |
| `text::tests::overflow_wrap_is_used_only_without_soft_opportunities` | 0.95 s |
| `text::tests::intrinsic_sizes` | 0.91 s |
| `text::tests::word_break` | 0.85 s |
| `text::tests::pre_wrap_example_three_ch` | 0.83 s |
| `text::tests::normal_wraps_after_spaces` | 0.83 s |
| the other 17 unit tests in `text::tests` | under 0.6 s each |

**WPT**: the `css/css-text/white-space/` and `css/css-text/line-breaking/`
tests are reftests and wait for the rendering harness of item 5.25.

### The box tree (item 5.13)

Golden test (`tests/golden_boxes.rs`): the 1,761 document cases of the
html5lib tree-construction suite vendored in `clazel-treebuilder`, parsed,
cascaded by `clazel_style::cascade` (item 5.7) under the user agent sheets in
an 800 by 600 viewport, built into box trees and printed (`boxes::dump`), one
fixture per `.dat` file under `tests/golden/boxes/`, compared byte for byte
(`CLAZEL_BLESS=1` regenerates them; review the diff). They hold 10,376 boxes:
510 anonymous, 403 split inline fragments and 1,142 text runs. The 206
`#document-fragment` cases and 6 scripted cases are not built. Natively the
test takes 2.6 s.

Unit tests (`src/boxes/tests.rs`, 29): box generation (`display: none` and
`contents`, text across inlines, white space collapsed away, `br` and `wbr`,
each replaced element, list markers with `start`, `value` and nested lists,
marker text per counter style); §9.2.1.1 (the section's own two examples,
empty sides of a split, nested inlines split together, consecutive blocks
and white space between them, inline blocks); each of §17.2.1's rules (1.1
to 1.4, 2.1 to 2.3, 3.1, 3.2 in a block, an inline and a cell), HTML tables
with HN's empty `<tr/>` and §17.4's captions; the grouping and split steps'
contracts; and a document of 100,000 nested elements (0.7 s natively),
built through `clazel-dom`'s own operations since the tree builder is
quadratic on such nesting. They use a hand-written style table, as the item
intends; the golden test runs the real cascade.

Kani harnesses (`src/boxes/proofs.rs`), measured as for item 5.12's below:
one harness at a time with `cargo kani -p clazel-layout --harness … --exact`,
each in its own process group capped at 20 minutes and 8 GB (resident set
of the whole group, polled every 5 s), on an Apple-silicon Mac. Times are
wall clock including cargo's start (the first includes building the crate
for Kani); memory is the larger of the 5 s samples and `time -l`'s peak.

| Harness | Kind | What it checks | Time | Peak memory |
|---------|------|----------------|------|-------------|
| `decide_any` | step, every size | what any node generates: only an element a principal box, only text a text run, `none` nothing, `contents` only for a non-replaced element, a replaced element no walked children | 16.3 s | 1.00 GB |
| `walk_step_any` | step, every size | one step of the generation walk from any frame satisfying its invariant: every frame pushed for any child satisfies it with the boxes added | 1.9 s | 0.22 GB |
| `group_step_any` | step, every size | the grouping step of stages 2 and 3 from any state: a wrapped child is never kept, a wrapper opened only when none is | 1.9 s | 0.21 GB |
| `irrelevant_any` | any input | stage 1 on any parent, child and siblings: rules 1.1 and 1.2 remove what they say, rules 1.3 and 1.4 only white-space-only text | 2.6 s | 0.22 GB |
| `stage_2_any` | any input | stage 2's decision for any parent and child meets the stage's goal (written a second time), in the parent and in the wrapper | 3.2 s | 0.22 GB |
| `stage_3_any` | any input | rules 3.1 then 3.2 for any parent and any child stage 2 left: no proper table child misparented, every cell in a row, an inline table in an inline | 3.4 s | 0.23 GB |
| `split_step_any` | step, every size | §9.2.1.1's split step from any state satisfying its invariant, any event: invariant kept, inline content placed with every fragment open, a block only with none open after every box has had its first fragment, an exited box's last fragment made | 2.3 s | 0.22 GB |
| `roman_any` | any value | Roman numerals: `None` exactly outside 1 to 3999, else weights adding up to the value | 7.6 s | 0.23 GB |
| `alphabetic_any` | any value | alphabetic numbering in base 26: `None` exactly below 1, 1 to 14 digits, each below 26 | 12.6 s | 0.77 GB |

**Proved for every size**: `generate::decide`, `generate::walk_step`,
`table::irrelevant_1`, `irrelevant_2`, `wrapper_2`, `wrapper_3_1`,
`wrapper_3_2`, `state::group_step` and `anonymous::split_step`: each loop
body of the passes, so a tree of any size and depth has each step's
properties. `marker::roman_counts` and `marker::alphabetic_digits` are proved
for every value. **Nothing is proved only for bounded inputs.**

Capped and removed (not retried): `regroup_any_3`, the grouping driver on
one parent with any 3 children, passed the 8 GB cap after 13.7 minutes of
symbolic execution, mostly in the drop glue of the arena's boxes.

**Not covered by Kani**: the drivers that walk the arena
(`generate::generate`, `table::stage_1` to `stage_3` with `regroup`,
`table::wrappers`, `anonymous::split`, `anonymous::text_runs`,
`BoxTree::compact`) as whole loops over trees, whose state is a vector of
boxes holding strings; reading the DOM and the computed style; the list
counters (`marker::ordinals`, a pass in tree order over a map) and the marker
strings; and Phase I, whose step item 5.12 proves. The unit and golden tests
run all of them. CI has not run these harnesses yet.

Miri: every test this item adds, one test per process with `cargo
+nightly-2026-08-21 miri test -p clazel-layout … --exact -Z unstable-options
--report-time`, each capped at 10 minutes. Times are on Miri's clock.

| Test | Miri time |
|------|-----------|
| `golden_boxes::golden_box_trees` (case 0 only: parsing the user agent sheets and one cascade dominate) | 107.2 s |
| `boxes::tests::deep_documents_build_without_recursion` (300 levels under Miri, 100,000 natively) | 48.3 s |
| `boxes::tests::list_items_get_markers` | 6.9 s |
| `boxes::tests::stage_3_2_misparented_children_get_tables` | 5.2 s |
| the other 26 tests in `boxes::tests` | under 5 s each |

**WPT**: the anonymous table objects tests (`css/CSS2/tables/` and
`css/css-tables/`) are reftests and wait for the rendering harness of item
5.25.

### Block and inline formatting (item 5.14)

Unit tests (`src/flow/tests.rs`, 36): documents parsed by the tree builder,
cascaded by item 5.7 with a user agent sheet of `display` values only, laid
out with `flow::BoxFont` (every glyph an em square, Ahem's metrics), each
expected position worked out by hand in a comment: each of §8.3.1's
adjoining pairs (siblings, parent and first child, last child and parent
with `height`, `min-height` and padding stopping it, a box collapsing through,
at its parent's top), its results for positive, negative and mixed margins
(Hacker News' `margin-bottom:-10px`), block formatting context roots,
inline blocks and the root element; §10.3.3's five rules and the
over-constrained cases, a negative `auto` width, §10.4; align descendants
(`center`, `div align=right`); §10.3.5's shrink-to-fit and an inline block's
baseline; replaced sizes; §10.5 percentages with the §3.5 quirk; §10.6 and
§10.7; §3.6 and §3.7; §10.8.1's example (`1.2`, `1.2em`, `120%`), the
half-leading, the strut with §3.4, §3.3 (a line holding a 1px image is 1px
high in quirks mode, 10px in no-quirks mode), each `vertical-align` value;
empty line boxes; wrapping and `br`; `text-align` (with `justify` and an
overflowing line) and `text-indent` (with §16.1's anonymous block rule);
inline boxes' edges; markers; the table placeholder; and a tree 100,000
blocks deep (300 under Miri).

Golden test (`tests/golden_flow.rs`): the 1,761 html5lib document cases
item 5.13's golden test builds, and two pages of our own
(`tests/golden/flow/pages/`: an HN-shaped table page in quirks mode, and a
page of margins, lists, inline blocks and lines), cascaded under the user
agent sheets in an 800 by 600 viewport, built into box trees and laid out in
real fonts (the vendored DejaVu Serif and Source Serif 4, matched with
Linux's generic families so the result is the same on every OS), printed by
`flow::dump` and compared byte for byte with `tests/golden/flow/`
(`CLAZEL_BLESS=1` regenerates them). They hold 8,108 fragments, 1,086 line
boxes and 1,174 glyph runs; the two pages were checked by hand against the
rules. Natively the test takes 2.6 s.

Kani harnesses (`src/flow/proofs.rs`), measured as for items 5.12 and 5.13:
one harness at a time with `cargo kani -p clazel-layout --harness … --exact`,
each in its own process group capped at 20 minutes and 8 GB (resident set
of the whole group, polled every 5 s), on an Apple-silicon Mac. Times are
wall clock including cargo's start; memory is the larger of the 5 s samples
and `time -l`'s peak.

| Harness | Kind | What it checks | Time | Peak memory |
|---------|------|----------------|------|-------------|
| `collapsed_any` | step, every size | the margin set: invariant kept, adjoining in any order gives the same set, union symmetric, one margin is itself, two follow §8.3.1's rule written a second time | 15 s | 0.70 GB |
| `enter_any` | step, every size | a child starts: the parent keeps nothing pending and does not move; the child opens exactly when its top adjoins its first child's | 5 s | 0.27 GB |
| `place_any` | step, every size | content placed after the frame's `y` and the margins; nothing left pending | 5 s | 0.27 GB |
| `close_any` | step, every size | an open frame closed at its top | 6 s | 0.26 GB |
| `exit_any` | step, every size | a child that collapsed through hands its margins on; a placed one moves `y` to its bottom | 5 s | 0.27 GB |
| `finish_any` | step, every size | §8.3.1's and §10.6.3's cases: collapse through only when open and allowed, with no content; nothing goes on past a bottom that does not adjoin | 5 s | 0.27 GB |
| `line_extent_any` | step, every size | a line box's extent: invariant kept, covers every box | 5 s | 0.27 GB |
| `solve_block_any` | any input | §10.3.3 never panics or overflows; the width is never negative | 5 s | 0.28 GB |
| `solve_block_sum` | any input within 2^22 px | the equality holds; a given width and `margin-left` are kept; two `auto` margins are equal to 1/64 px | 20 s | 0.28 GB |
| `align_any` | any input within 2^22 px | align descendants keeps the width and the margins' sum, and moves only a forced box | 5 s | 0.27 GB |
| `width_min_max_any` | any input | §10.4's steps 2 and 3 | 5 s | 0.27 GB |
| `shrink_to_fit_any` | any input | §10.3.5's formula, never negative for non-negative sizes | 5 s | 0.27 GB |
| `heights_any` | any input | §10.7 (`min-height` wins, never negative), the fill quirks, the percentage basis | 5 s | 0.27 GB |
| `half_leading_any` | any input (equation within 2^22 px) | §10.8.1: the halves add up to the line height, the upper one rounded down | 10 s | 0.27 GB |
| `align_offset_any` | any input | §16.2: the content stays in the line box when it fits, start-aligned when it does not | 6 s | 0.27 GB |
| `role_any` | any class | what each box is to the walk | 5 s | 0.27 GB |
| `halves_any` | any value | a length's two halves add up to it | 5 s | 0.26 GB |
| `times_any` | any value | a number times a length (`line-height: <number>`) never overflows | 5 s | 0.27 GB |

**Proved for every size**: the margin set (`Collapsed::of`, `adjoin`,
`join`, `resolve`), each step of a block container's flow
(`margins::enter`, `place`, `close`, `exit`, `finish`, with
`BlockFacts::top_adjoins`, `bottom_adjoins`, `may_collapse_through`) and
`LineExtent::add`: the state each block container and each line box carry,
so a tree of any size and depth has each step's properties. **For every
input**: `widths::solve_block`, `align`, `min_max`, `shrink_to_fit`,
`heights::min_max`, `quirk_fill`, `child_basis`, `half_leading`,
`inline::align_offset`, `block::role`, `length::half_down`, `half_up`,
`times`. **Only for bounded inputs**: §10.3.3's equality and §10.8.1's sum,
on values within 2^22 px (beyond it they saturate, which `solve_block_any`
and `half_leading_any` check is panic-free). No harness hit a cap; none was
removed.

**Not covered by Kani**: the drivers (`block.rs`'s walk and its resolution
walk over the frame stack, `inline.rs`'s preparation, line building and
vertical alignment loop, `intrinsic.rs`'s pass), whose state is the arena,
the frames and the fragment vectors; reading style and fonts; item 5.12's
line choice (proved there). The unit and golden tests run all of them. CI
has not run these harnesses yet.

Miri: every test this item adds, one test per process with `cargo
+nightly-2026-08-21 miri test -p clazel-layout … --exact -Z unstable-options
--report-time`, each capped at 10 minutes and run alone under the shared
lock. Times are on Miri's clock; all 37 passed.

| Test | Miri time |
|------|-----------|
| `golden_flow::golden_fragment_trees` (case 0 only, no page: the user agent sheets and one cascade dominate) | 109.4 s |
| `flow::tests::vertical_align` (seven documents) | 40.9 s |
| `flow::tests::text_align` (six documents) | 38.8 s |
| `flow::tests::last_child_and_parent_bottom` | 27.9 s |
| `flow::tests::inline_blocks_shrink_to_fit` | 23.0 s |
| `flow::tests::margins_collapse_through_an_empty_box` | 22.2 s |
| `flow::tests::deep_trees_lay_out_without_recursion` (300 levels under Miri, 100,000 natively) | 8.7 s |
| the other 30 tests in `flow::tests` | under 21 s each |

**Performance not bounded**: a line's inline boxes are found by walking up
from its units, so a paragraph nested *n* inline boxes deep over *L* lines
costs about *n* × *L*; item 5.26's hostile pages will measure it.

**WPT**: the `css/CSS2/` reftests the item names (`normal-flow`,
`margin-padding-clear`, `box-display`, `linebox`, `visudet`, `visuren`) wait
for the rendering harness of item 5.25.
