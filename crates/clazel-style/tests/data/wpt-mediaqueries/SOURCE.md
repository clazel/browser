# WPT media queries tests, for the features of Phase 5's subset

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/css/mediaqueries
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The same WPT commit as the other suites of `clazel-css`, `clazel-selectors` and
`clazel-style`. Each page is copied byte for byte from `css/mediaqueries/` under its own
name. To update, copy the same pages from a newer commit, change the commit above, and run
`cargo xtask testdata`.

**Which pages** (phase-5.md item 5.8: the media types `all`, `screen` and `print`, `not`,
`only`, `and`, `or`, comma lists, and the `width`, `height` and `orientation` features):

- `test_media_queries.html`, the self-contained suite (its helpers call the page's iframe;
  its other tests compute their queries in loops, see below);
- `match-media-parsing.html`, which serializes `matchMedia(query).media`;
- the reftests on syntax, types, `not`, `only`, `or`, ranges and lengths:
  `mq-invalid-media-type-001` to `-006`, `mq-invalid-media-type-layer-001` and `-002`,
  `negation-001` and `-002`, `mq-range-001`, `mq-negative-range-001` and `-002`,
  `media-queries-001` to `-003` (`.xht`), `min-width-001.xht`, `mq-deprecated-001` and
  `relative-units-001` to `-004`. Their references are a green square or a green page, and
  on each of them an `@media` rule whose block paints green must apply and one that paints
  red must not, in WPT's 800 by 600 viewport.

Not vendored: `mq-case-insensitive-001.html`, whose first two red `@media` rules do apply
(one of them always matches) and are overridden by the green rules after them, which only
the cascade (item 5.7) and the reftest harness (item 5.25) can check; the pages on features
outside the subset (`aspect-ratio-*`, `device-aspect-ratio-*`, `mq-calc-*`, `mq-gamut-*`,
`prefers-*`, `forced-colors`, `dynamic-range`, `scripting*`, `display-mode*`, `update`,
`overflow-media-features` and the rest); and the pages that need script, an iframe or
CSSOM objects beyond what these tables read (`media-query-matches-in-iframe`,
`viewport-script-dynamic`, `nested-media-queries`, `mq-escaped-serialization`,
`mq-unknown-feature-custom-property`, `at-custom-media-*`, ...).

`xtask/src/testdata/wpt_mediaqueries.rs` converts them into
`tests/generated/wpt_mediaqueries.rs`. `test_media_queries.html` is read **call by call**:
a call of one of its six helpers that is a statement of `run()`'s body, outside any loop,
condition or nested function, with one string literal argument that substitutes nothing, is
a case; every other use of a helper is listed by line as not run, with the reason. The
iframe's size is followed through its literal assignments, from the default 300 by 150.
`match-media-parsing.html` is read the same way (its calls inside
`test_resolution_parsing()` are not run). The reftests give the text of each `style`
element (with an XHTML page's CDATA markers removed) and each `@media` rule's colour.
