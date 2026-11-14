# WPT css-cascade tests that read computed values, for Phase 5's subset

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/css/css-cascade
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The same WPT commit as the other suites of `clazel-css`, `clazel-selectors` and
`clazel-style`. Each page is copied byte for byte from `css/css-cascade/` under its own
name. To update, copy the same pages from a newer commit, change the commit above, and run
`cargo xtask testdata`.

**Which pages** (phase-5.md item 5.7: the sort order, presentational hints, defaulting and
computed values): the testharness.js pages of `css/css-cascade/` with at least one test
that only reads `getComputedStyle` values and compares them, in the form
`xtask/src/testdata/wpt_css_cascade.rs` reads:

- `important-vs-inline-001.html` and `-002.html` (`!important` against the `style`
  attribute; their other tests change the attribute from script and are not run);
- `inherit-initial.html` (`inherit` on the root element);
- `presentational-hints-cascade.html` (hints below author rules and the `style`
  attribute);
- `revert-val-005.html` (`revert` on physical and flow-relative margins);
- `revert-val-006.html` (`revert` in `@keyframes`, which this phase does not run) and
  `revert-val-011.html` (`left`, outside the subset): each test reads, and fails for the
  reason the conformance test prints.

**Not vendored**, and why:

- the reftests (`important-prop`, `initial-color-background-001`, `unset-val-001` and
  `-002`, `revert-val-001` and `-002`, `all-prop-*`, `revert-layer-*`, `scope-*`, `layer-*`
  and the rest): phase-5.md item 5.7 runs them through item 5.25's reftest harness, which
  does not exist yet;
- testharness.js pages none of whose tests read in that form: `important-vs-inline-003`,
  `revert-val-003`, `-004`, `-007` to `-010` (script changes to the DOM, style or
  animations, `all`, loops), `unset-value-storage` and `declaration-context` (CSSOM rule
  objects), `duplicate-stylesheets` (sheets added from script), `inline-style-background`
  (a crash test), `presentational-hints-rollback` (`check-layout-th.js` and layout);
- everything about `@layer`, `@scope`, `@import`, the `all` shorthand, `revert-rule` and
  the CSSOM, which are outside the subset (5.0(b)).

`xtask/src/testdata/wpt_css_cascade.rs` converts the pages into
`tests/generated/wpt_css_cascade.rs`: each test that holds only `offsetTop`/`offsetLeft`
reads, `let NAME = getComputedStyle(TARGET).PROPERTY` bindings and `assert_equals` or
`assert_not_equals` on such values and string literals is a case; every other test is
listed by line with the first statement not read.
