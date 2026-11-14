# The HN-shaped fixture (phase-5.md items 5.25 and 5.26)

`index.html` and `site.css` are a page and a sheet written for this project,
under the repository's MIT licence, so they can be vendored, served, laid out
and screenshotted. Their text is invented ("Lanterns", a made-up link
aggregator; every title, name and remark is fiction), and nothing in them is
copied from the real site or its sheet: the real pages and their sheet are
Y Combinator's and their users', and are not vendored (phase-5.md 5.1, 5.26).

What they reproduce is the *shape* of the exit pages: the structures, attributes,
selectors, properties and at-rules the plan measured. The source of those
shapes is phase-5.md's "What the exit page needs" (measured on 2026-10-31,
by counting tags, attributes, inline styles, selectors and properties): item
5.1's inventory script, which would write `docs/phase5-inventory.md`, has not
been run in this repository, so that section is the measurement used. When
5.1's script runs, anything it finds that this fixture lacks should be added.

## What each shape is there for

| Shape | Where | Why it is here |
|-------|-------|----------------|
| No `<!DOCTYPE>`: quirks mode | `index.html`'s first line | The exit pages are in quirks mode: the Quirks Mode Standard's line height, fill and table quirks (5.14, 5.15) and HTML's quirks sheet (tables do not inherit `font-size`, which is why the sheet repeats its `body` rule for `td`). |
| Tables nested four deep | `#frame` > masthead table; > listing; > discussion > per-remark tables | Table layout (5.15) carries the whole page: auto layout, nested shrink-to-fit, percentage widths. |
| `width="85%"`, `bgcolor`, `border="0"`, `cellpadding="0"`, `cellspacing="0"` | `#frame` | Presentational hints (5.7: HTML §15.3.8) and a percentage-width table centred by `center`. |
| `min-width:796px` on the outer table | `site.css` (`#frame`, `.listing`) | `min-width` on tables (5.15). |
| `center` | around `#frame`, the vote arrows, the footer | HTML's "align descendants" and `text-align: center` (5.14). |
| `align="right"`, `valign="top"`, `colspan="2"` | listing rows | Cell alignment, `vertical-align` from `valign`, column spans (5.15). |
| Rows with only `style="height:5px"` (and `10px`) | `.spacer`, `#gap`, `.morespace` | Empty rows sized by `height` alone (5.13's anonymous objects, 5.15's row heights). |
| An 18×18 image with a white 1px border, `display:block` | the masthead | A replaced box sized by attributes with a border (5.13, 5.14, 5.16). |
| Spacer images `s.gif` with `height="1"` and `width` 0, 40, 80 | each remark's `.indent` cell | The remark tree's indentation, and the line height quirk for a line holding only an image. |
| `font size="1"`, `font color` | each reply link; the third remark | `font`'s presentational hints (HTML §15.3.4). |
| `u`, `i`, `b`, `br`, `p`, `pre`, `code`, `span`, `div`, `a` | throughout | The element set the measurement found. |
| Inline `style`: `height:…`, `margin-top:2px; margin-bottom:-10px;`, `padding`, `text-align`, `line-height`, `display:block`, `border:1px white solid` | rows, the remark heads, masthead cells, the image | Style attributes (5.8) and negative margins (5.14's margin collapsing). |
| A `form` with `input` (`hidden`, `submit`, `text` with `readonly`) and `textarea` | the remark form, the search | Form controls as replaced boxes sized by `size`, `cols` and `rows` (5.13, 5.14). |
| One external sheet: `<link rel="stylesheet" type="text/css" href="site.css?v=7">`, same origin, with a query | `<head>` | A style sheet fetch (5.19) and its `type`. |
| Type, class, ID, descendant and child selectors, `span.masthead` compounds, lists, attribute selectors `input[type='submit']`, `input[readonly]`, `:link`, `:visited`, `:hover` | `site.css` | The selector shapes (5.5). The child combinator (`.titleline > a`) is one the real sheet lacked; it is kept to cover the selector engine. |
| `font-family` lists with `monospace`, `font-size` in `pt`, `px` and `inherit`, hex `color`, `background` and `background-color`, `text-decoration`, margins and padding with longhands (negative included), `border`, `width`, `min-width`, `max-width`, `height`, `line-height`, `text-align`, `vertical-align`, `display` (`none`, `block`, `inline-block`), `visibility`, `overflow`, `white-space` (`pre-wrap`, `nowrap`), `overflow-wrap: anywhere`, `word-break: break-word`, `text-overflow`, `resize`, `cursor`, `pointer-events`, `transform` (with vendor prefixes), `page-break-before`, `background` with `url()` and `linear-gradient()`, `!important` | `site.css` | The properties and values the measurement found, including those 5.6 parses without effect. |
| Eleven `@media only screen and (min-width: …) and (max-width: …)` rules, and one on `-webkit-min-device-pixel-ratio` and `min-device-pixel-ratio` | the end of `site.css` | Media queries on width (5.8): the remark width changes with the viewport; the device pixel ratio query parses and does not match at scale 1. |
| `&amp;` in `href`s, `&nbsp;` | the listing | Character references in attributes and text (Phase 4's tokenizer). |

The images (`mark.gif`, `s.gif`, `triangle.svg`) and the favicon are not
here: Phase 5 decodes no image, and an `img` is a box of its attributes' size.

## `screenshot-macos-metal.png`

The page as `clazel --headless OUT --size 800x600 URL` wrote it on
2026-11-13, served with its sheet (`site.css?v=7`) from loopback: macOS 26.7.2
on an Apple M1 Pro, Metal, at commit `9006b6e9` of `claude/sheets-wired`, with
`browse`'s own fonts (`RENDERER_FONTS` in `cli/window.rs`: the system's Arial,
Arial Bold, Times New Roman and Courier New). It was stored because three runs
gave byte-identical files (SHA-256
`89d079fc3f547c50fbfa5d7e752e8e4b51ed274d01825253f943b44187d0e955`).

Nothing compares against it yet. It shows what this machine draws. It is not a
reference for other machines: other system fonts or another GPU change pixels.
CI's exact comparison runs on lavapipe (Mesa's software Vulkan), a different
driver, so it needs its own stored image, made by CI's job (5.25).
