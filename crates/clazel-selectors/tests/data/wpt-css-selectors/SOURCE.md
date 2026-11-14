# WPT `css/selectors/parsing/`, the official selector parsing tests

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/css/selectors/parsing
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The 24 pages here are copied byte for byte from `css/selectors/parsing/` at that
commit, the same WPT commit as `clazel-css`'s and `clazel-encoding`'s suites, and
`parsing-testcommon.js` from `css/support/`, which says what the helpers mean. To
update, copy them from a newer commit, change the commit above, and run
`cargo xtask testdata`.

`xtask/src/testdata/wpt_css_selectors.rs` converts them into
`tests/generated/wpt_css_selectors.rs`. `tests/wpt_table.rs` checks the table; item
5.5's conformance test will run it.

**What the table holds:** every helper call of every page, with its selector, whether
it is valid, and what it may serialize to. Two pages write their cases as templates,
which the converter expands as the page's own script would: `parse-is-where.html` runs
each case for `:is` and `:where`, and `parse-anplusb.html` runs each case for four
`:nth-` pseudo-classes. Both are read literally, so a change to either template fails
the conversion.

**Not run:** one direct `test()` in `parse-has-disallow-nesting-has-inside-has.html`,
which checks `matches()` through the DOM. The table's `NOT_RUN` lists it.

Item 5.5 must allow for these:

- **Many cases are outside the phase's subset.** `:has()`, `::part()`, `::slotted()`,
  `:state()`, `:heading` and `:focus-visible` have pages here, and `:has()` is out of
  Phase 5 (phase-5.md item 5.5). Such a case becomes an expected failure with its
  reason. None of them is a pass.
- **Two pages are `.tentative`.** Their behaviour is not settled in a standard.
- **Results are what a browser's object model serializes.** The expected text is
  `selectorText`, so a case checks "serialize a selector" as well as parsing.
- **`parse-anplusb.html` has its own helpers**, `assert_selector_serializes_to` and
  `assert_invalid_selector`, which check `sheet.cssRules` and not `querySelector`.
  The table keeps each case's helper, so the difference stays visible.
- **`test_valid_forgiving_selector`** means valid only where the selector is forgiving:
  `:is()` and `:where()`. It is not the same as `test_valid_selector`.

Not vendored, for now: the rest of `css/selectors/`, which is mostly reftests and DOM
tests, for items 5.5 and 5.25, and `WEB_FEATURES.yml`.
