# WPT property value parsing pages, for the properties of Phase 5's subset

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/css
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The same WPT commit as `clazel-css`'s and `clazel-selectors`' suites. Each page is copied
byte for byte; its name keeps its directory as a prefix, so `css-box.margin-valid.html` is
`css/css-box/parsing/margin-valid.html` and `css-values.calc-invalid-parsing.html` is
`css/css-values/calc-invalid-parsing.html`. `parsing-testcommon.js` is
`css/support/parsing-testcommon.js`, which says what the helpers mean: `test_valid_value`
sets `element.style[property]` and reads `getPropertyValue(property)` back, which must be
one of the expected strings; `test_invalid_value` expects the empty string. To update, copy
the same pages from a newer commit, change the commit above, and run `cargo xtask testdata`.

**Which pages.** For each property of the subset (phase-5.md item 5.6, and the "parsed, no
effect" ones that have pages), the `-valid` and `-invalid` pages of its defining
specification's `parsing/` directory: `css-box` (margin, padding, visibility), `css-sizing`
(width, height and their `min-` and `max-`), `css-display`, `css-overflow` (overflow,
text-overflow), `css-fonts` (font-family, font-size, font-style, font-weight, font),
`css-inline` (line-height, vertical-align), `css-text` (text-align, text-indent,
white-space, overflow-wrap, word-break), `css-text-decor` (text-decoration and its
longhands), `css-backgrounds` (background-color, background, background-image and the
border properties), `css-tables` (border-collapse, border-spacing, table-layout),
`css-lists` (list-style-type), `css-ui` (cursor, resize) and `css-color` (the pages for
hex, named, `rgb()` and `hsl()` colours). From `css-values`, three pages that try value
syntax on properties of the subset. `pointer-events`, `transform` and `page-break-before`
have no parsing pages in the directories above and are not vendored.

`xtask/src/testdata/wpt_css_values.rs` converts them into
`tests/generated/wpt_css_values.rs`. **A page is read only if every call of the two
helpers is at the top level of its script with literal arguments**; a page that calls them
from a loop, a function or with computed arguments is listed in the table's `NOT_RUN` with
the reason, and none of its cases count. Calls of other helpers (`test_shorthand_value`,
`test_computed_value`, a page's own wrappers) are counted in `OTHER` and not run.
