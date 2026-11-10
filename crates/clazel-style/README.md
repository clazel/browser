# clazel-style

CSS style for Clazel's Phase 5 browser (`docs/phases/phase-5.md`, items 5.6 and 5.7). Part
of [Clazel](../../README.md), a web browser whose parsers of untrusted input carry
machine-checked proofs.

Item 5.6 is the module `values/`: the property value grammars of the CSS subset Phase 5
needs (5.0(b): what the Hacker News exit page uses), shorthands, the Quirks Mode Standard's
value quirks, and CSSOM's serialization. Item 5.7's cascade will be the module `cascade/`.

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
