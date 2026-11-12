# clazel-style

CSS style for Clazel's Phase 5 browser (`docs/phases/phase-5.md`, items 5.6 to 5.8). Part
of [Clazel](../../README.md), a web browser whose parsers of untrusted input carry
machine-checked proofs.

Item 5.6 is the module `values/`: the property value grammars of the CSS subset Phase 5
needs (5.0(b): what the Hacker News exit page uses), shorthands, the Quirks Mode Standard's
value quirks, and CSSOM's serialization. Item 5.8 is the module `sources/`: what style sheets
a document has, in order, which apply, each element's `style` attribute, and media queries.
Item 5.7's cascade will be the module `cascade/`.

## What it reads

A declaration's value comes from `clazel-css` as component values ("parse a list of
component values", CSS Syntax 3 §5.4), which `values/items.rs` flattens. Each property's
grammar then reads them and gives the value as components in CSSOM's order;
`values::parse(name, value, quirks)` gives the longhands a declaration sets, or `None` if
the property is unknown or the value invalid (the declaration is then dropped, as CSS
Syntax says), and `values::get_property_value` is CSSOM's `getPropertyValue`.

**Applied in Phase 5** (each grammar is cited to its specification in the source):

| Property | Grammar |
|----------|---------|
| `color`, `background-color`, `border-*-color`, `border-color` | `<color>`: hex (3, 4, 6, 8 digits), the 148 named colours, `rgb()`/`rgba()` and `hsl()`/`hsla()` in the legacy and modern syntaxes, `transparent`, `currentcolor` |
| `margin`, `margin-*` | `<length-percentage> \| auto`, 1 to 4 values |
| `padding`, `padding-*` | `<length-percentage [0,∞]>`, 1 to 4 values |
| `border-*-width`, `border-width` | `<line-width>` |
| `border-*-style`, `border-style` | `<line-style>`: every style is parsed; layout draws them `solid` |
| `border`, `border-top` … `border-left` | `<line-width> \|\| <line-style> \|\| <color>` |
| `width`, `height`, `min-*`, `max-*` | `auto` (`none` for `max-*`) `\| <length-percentage [0,∞]>` |
| `display` | `none`, `block`, `inline`, `inline-block`, `list-item` and the table values |
| `overflow`, `overflow-x`, `overflow-y` | `visible \| hidden \| clip \| scroll \| auto`, 1 or 2 values |
| `visibility` | `visible \| hidden \| collapse` |
| `font-family` | family names (strings or identifiers) and the generic families, comma-separated |
| `font-size` | the absolute and relative keywords, `<length-percentage [0,∞]>` |
| `font-weight`, `font-style` | CSS Fonts 4's, with `oblique <angle>` |
| `font` | style, small-caps, weight and width keywords, size, `/ line-height`, family |
| `line-height` | `normal \| <number [0,∞]> \| <length-percentage [0,∞]>` |
| `vertical-align` | CSS 2.1 §10.8.1's keywords and `<length-percentage>` |
| `text-align` | CSS Text 3's keywords |
| `text-decoration`, `-line`, `-style`, `-color` | CSS Text Decoration 3 (and Level 4's `-thickness`, parsed) |
| `text-indent` | `<length-percentage> && hanging? && each-line?` |
| `white-space`, `overflow-wrap` (`word-wrap`), `word-break` | CSS Text 3's keywords |
| `border-spacing`, `border-collapse`, `table-layout` | CSS 2.1 §17 |
| `list-style-type` | `<counter-style-name> \| <string> \| none` |
| `background` | one layer: colour, image, position `/` size, repeat, attachment, boxes |

**Parsed, no effect in Phase 5** (HN uses them; a later phase adds only their effect):
`cursor` (`<url>` with hotspot, and the keywords), `pointer-events`, `resize`, `transform`
(`none` and the 2D functions of CSS Transforms 1), `page-break-before`, `text-overflow`
(one value), `background-image` (`none`, `<url>`, `linear-gradient()` and
`repeating-linear-gradient()`), `background-repeat`, `background-attachment`,
`background-position` (one or two values), `background-size`, `background-origin`,
`background-clip`, `font-variant-caps`, `font-stretch`, `text-decoration-thickness`, and
the border styles other than `solid` and `none` (drawn `solid`).

**Not in the subset, so invalid and dropped:** `calc()` and the other math functions,
`var()`, viewport and container units, the intrinsic sizing keywords (`min-content`,
`max-content`, `fit-content()`), `display`'s other values and its multi-keyword syntax,
CSS Inline 3's `vertical-align` forms, colour spaces other than sRGB (`hwb()`, `lab()`,
`color()`, `color-mix()`, relative colours, `light-dark()`, system colours), `image-set()`,
`cross-fade()`, several background layers, the 3- and 4-value background positions, the
system font keywords, `symbols()`, Level 4 keywords of `text-decoration-line` and
`word-break`, every other property, and vendor-prefixed properties.

The modelling choices are listed at the top of `src/values/mod.rs`: numbers are
millionths in an `i64`, rounded once from the token's exact value and clamped to ±10^9;
used lengths (`values::number::to_px64`) are 1/64 px in an `i32`, rounded to nearest (ties
away from zero) and clamped to ±(2^30 − 1), with `ex` taken as 0.5 em; colours resolve to
8-bit sRGB when parsed, keeping a named colour's name; and the quirks apply only to the
properties the Quirks Mode Standard lists, when set directly.

## Style sources and media queries (item 5.8)

`sources::collect(&arena)` reads a document's `clazel-dom` arena once, in tree order, and
gives its `Sources`:

- **`<style>` elements**: HTML §4.2.6 "update a style block": skipped if `type` is present
  and neither empty nor `text/css`; the sheet is the element's child text content, parsed
  by `clazel-css` ("parse a stylesheet", CSS Syntax 3 §5.4.3).
- **`<link rel=stylesheet>` elements**: rel's tokens include `stylesheet`, `href` is present
  and not empty, `disabled` is absent, and `type`, if present, is `text/css` (HTML §4.2.4.2,
  §4.6.8.23). Each is `Pending` until the renderer hands its response to
  `Sources::link_loaded` (the `Content-Type` header, whether it is same-origin, whether the
  fetch succeeded, and the body). That runs §4.6.8.23 "process this type of linked
  resource": a `Content-Type` other than `text/css` fails the sheet, **except in quirks
  mode for a same-origin sheet**, which is taken as `text/css`; the body is decoded with the
  `charset` parameter, then the link's `charset` attribute, then the document's encoding.
- **`style` attributes** of every element: CSS Style Attributes §3, parsed as a list of
  declarations (CSS Syntax 3 §5.4.5), kept per element for the cascade's element-attached
  step.
- **Titles and alternate sheets**: CSSOM §6.2 "add a CSS style sheet", in tree order, so the
  first titled sheet sets the preferred set and other titled sets and alternates are
  disabled.

A sheet's rules (`sources::sheet::StyleSheet`) are its style rules in order, each with its
selector text (for `clazel-selectors`), its declarations (name, value as `values/` items,
`!important`) and the innermost `@media` rule around it; nested `@media` rules point at
their parent. `Sources::rules_for(device)` gives the style rules that apply on a device, in
the cascade's order of appearance: enabled sheets whose `media` matches, in tree order, and
within each the rules whose `@media` rules all match.

**Recognised and ignored**, with everything inside them: `@import`, `@supports`,
`@font-face`, `@namespace` and `@page` (listed in `StyleSheet::ignored`). Other at-rules,
`@charset` included, are dropped as CSS Syntax says. Not read: rules nested in a style rule
(CSS Nesting) and declarations directly inside `@media`.

**Media queries** (`sources::media`, Media Queries 4, W3C CRD of 8 October 2026): the media
types `all`, `screen` and `print` (the deprecated types parse and match nothing), `not` and
`only`, `and`, `or` and `not` in conditions with parentheses, comma lists, and the features
`width` and `height` (plain, `min-`/`max-`, and the range forms `(400px <= width < 700px)`)
and `orientation`, against the viewport, with `em`, `rem` and `ex` from the initial 16 px
font size. Evaluation is Kleene's three-valued logic (§3.1): any other feature, value or
syntax that reaches `<general-enclosed>` is unknown, so a query that needs it is false,
and so is its negation. That is what HN's `-webkit-min-device-pixel-ratio` and
`min-device-pixel-ratio` query gets. Lists serialize as CSSOM §4.2 says, extended to Level
4's conditions.

**Not here, left to later items**: the fetches (5.19) and the renderer's use of the sources
(5.20: sending a request for each pending link, waiting for them, re-evaluating `media` on a
new viewport, feeding `rules_for` to the cascade). `clazel-renderer` is not changed by 5.8.

**Decisions taken** (from phase-5.md's plan, the maintainer being away):

- The interface takes fetched sheets as input (bytes plus the response facts the quirk
  needs) and exposes the ordered rule list, since 5.19 and 5.20 are not started.
- Range syntax (`width >= 600px`) and `or` are implemented with the rest of Level 4's
  condition grammar: they are part of the `width` feature and of conditions, and cost
  little. Other features stay unknown, as item 5.8 says.
- A media query list is split at every top-level comma after trimming whitespace (so
  `foo,` is `foo, not all`), and an unknown query is kept rather than replaced with
  `not all`; both follow WPT and engines where the specifications read literally say
  otherwise, and both are in `docs/ERRATA.md`.
- Titles, alternates, `disabled` and `type` are handled as HTML and CSSOM say, though HN
  uses none of them; Content Security Policy is not implemented; SVG's `style` element is
  not read.
- Nesting of `( … )` in a media condition is bounded at 32 levels (deeper ones are
  `<general-enclosed>`, unknown), so the parser's recursion is bounded on hostile input.

The modelling choices are listed at the top of `src/sources/mod.rs` and
`src/sources/media.rs`.

## Verification

Tier 0 now, target tier 1 (phase-5.md 5.0(a)): the tier is raised only after CI's full
verification of the harnesses is green.

- **Kani harnesses** (`src/values/proofs.rs`): each runs one operation on every input
  within its bound, checking for panics, overflow, reads outside a slice and loops that
  pass their bound. All 18 pass locally (Kani 0.68, one harness at a time; about 27
  minutes in all, peak 10.4 GB):

  | Harness | Bound | Time | Peak memory |
  |---------|-------|-----:|------------:|
  | `cursor_bump_any_4` | any cursor over any 4 items: moves forward, inside its list | 6 s | 0.3 GB |
  | `cursor_function_any_4` | the same, and the argument cursor is inside its parent | 10 s | 0.3 GB |
  | `cursor_one_item_steps_any_4` | ident, keyword, comma, delim: one item or none | 26 s | 0.8 GB |
  | `table_lookup_any_20` | a table lookup's loop body, any string of up to 20 code points | 6 s | 0.3 GB |
  | `cursors_any_13` | the cursor keywords, any string of up to 13 | 183 s | 2.1 GB |
  | `units_and_wide_keywords_any_12` | units, CSS-wide keywords, reserved idents, up to 12 | 42 s | 1.1 GB |
  | `length_any_1` | `<length>`, `<length-percentage>`, any range, quirky or not, any 1 item | 15 s | 0.8 GB |
  | `number_percentage_angle_any_1` | `<number>`, `<percentage>`, `<angle>`, any 1 item | 5 s | 0.3 GB |
  | `url_string_ident_any_2` | `<url>`, `<string>`, `<custom-ident>`, any 2 items | 61 s | 2.4 GB |
  | `color_any_1` | `<color>`, quirky or not, any 1 item but an identifier | 179 s | 9.3 GB |
  | `rgb_args_any_5` | `rgb()`'s arguments, any 5 items | 521 s | 9.8 GB |
  | `hsl_args_any_5` | `hsl()`'s arguments, any 5 items | 535 s | 10.4 GB |
  | `hex_any_8` | hex notation and the quirky ident, any string of up to 8 | 6 s | 0.4 GB |
  | `quirky_number_any_7` | the quirky number, any digits and unit of up to 7 each | 13 s | 0.9 GB |
  | `number_conversion_clamps` | a token's value, any 4-code-point number and exponent parts: within ±10^9 | 4 s | 0.4 GB |
  | `lengths_convert_and_clamp` | any length, unit and font sizes, and any percentage, to 1/64 px: within ±(2^30 − 1) | 9 s | 0.9 GB |
  | `angles_convert_and_clamp` | any angle to degrees: within ±10^9 | 1 s | 0.2 GB |
  | `hsl_converts` | HSL to RGB, any hue, saturation, lightness | 7 s | 0.8 GB |

  Every value text is any 3 code points (spans are arbitrary, so every shorter string is
  a span of it). **Not done** (each exceeds 20 minutes or 12 GB locally even at small
  bounds; covered only by the unit tests and the conformance test below): each
  longhand's and shorthand's whole grammar on any sequence of items (four ran 5 h 48 min
  at one item without finishing); the named-colour and counter-style tables run whole,
  and `<color>` on an identifier; `rgb()` and `hsl()` with seven items (`hsl()` verifies
  in 18 minutes at 14 GB); `Values::from_rows`, which calls `clazel-css`'s tokenizer (one
  row over one code point exceeds 5 minutes; the tokenizer is proven by Verus in that
  crate); and serialization.
- **Conformance** (`tests/conformance_values.rs`), over the vendored WPT data
  (`tests/data/`, both at WPT commit `4ad507b2`):
  - the `-valid` and `-invalid` parsing pages of the subset's properties: 912 cases, run
    as `parsing-testcommon.js` runs them (set, read back, set again): **702 pass, 210
    expected failures** (each listed with its reason, all syntax outside the subset), none
    fail. Nine pages call the helpers from loops or wrappers and are not run, and 64 calls
    of other helpers (`test_shorthand_value` and the like) are not run; the table lists
    both.
  - `quirks/unitless-length` and `quirks/hashless-hex-color`: every case on every property
    of the subset, in quirks, limited-quirks and no-quirks mode: **10,714 pass, 183
    expected failures** (`calc()`), none fail. The pages compare computed values; until
    5.7 the test compares the serialized specified values, which is the same check where
    the reference is written as the value the quirk gives. Properties outside the subset
    (`top`, `left`, `clip`, `letter-spacing`, `word-spacing`, `outline-*`, …) and the SVG
    half are not run.

### Item 5.8 (`sources/`)

- **Kani harnesses** (`src/sources/proofs.rs`), measured locally one at a time (Kani 0.68,
  macOS arm64, wall time including the build, peak resident memory of the run's process
  group sampled every 5 s):

  | Harness | Bound | Time | Peak memory |
  |---------|-------|-----:|------------:|
  | `kleene_any` | §3.1's `not`, `and`, `or` on every pair of the three values, with Kleene's laws | 6 s | under 0.1 GB |
  | `feature_any` | any `<media-feature>` (any name, prefix, test, comparisons, numbers, units, identifiers) on any device | 36 s | 3.1 GB |

  **Not done** (covered only by the unit tests and the conformance test below): the
  condition evaluator on any list of four ops, even with features reduced to unknown
  names (over 8 GB in 69 s); a query of up to three ops (over 8 GB in 118 s); a list of up
  to three one-op queries (over 8 GB at 686 s); the parser on any four tokens (unfinished
  after 12 minutes); the tokens adapter, which calls `clazel-css`'s tokenizer; the
  serializer; and the sheet walk and document collection. Each was stopped at the local
  8 GB cap and removed rather than sent to a 16 GB CI runner untested.
- **Conformance** (`tests/conformance_mediaqueries.rs`), over WPT `css/mediaqueries/` at
  commit `4ad507b2` (`tests/data/wpt-mediaqueries/SOURCE.md`):
  - `test_media_queries.html`, read call by call: **159 pass, 55 expected failures**, none
    fail, of 214 calls read; 159 calls are not run (in loops, conditions or functions, or
    with computed strings) and are listed by line with the reason.
  - `match-media-parsing.html`: **21 pass**, none fail; the 13 calls inside
    `test_resolution_parsing()` are not run.
  - 22 reftests, one unit per `@media` rule: **47 pass, 10 expected failures**, none fail.
  - Every expected failure is a query on a media feature outside the subset (`color`,
    `monochrome`, `aspect-ratio`, `device-*`, `color-index`, `scan`, `grid`,
    `overflow-*`, `update`, `hover`, `pointer` and their `any-` forms) or the `ch` unit,
    each listed with its reason when the test runs.
- **Miri** (`--report-time`, Miri's clock, nightly-2026-08-21, locally): the whole crate
  passes, 37 tests in about 181 s of Miri time, none over 42 s. Under `cfg!(miri)`
  `test_media_queries.html` runs every fourth case (each tokenizes and parses one or two
  short strings): 18 s; the reftests run whole in 35 s and `match-media-parsing.html` in
  2.5 s. `deep_nesting_is_bounded` nests 1,000 levels under Miri instead of 100,000: 15 s,
  where 100,000 passed 10 minutes without finishing (and ran out CI's 6-hour Miri job on
  the first push of this branch).
