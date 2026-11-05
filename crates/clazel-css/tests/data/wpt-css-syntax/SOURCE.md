# WPT `css/css-syntax/`, the official CSS Syntax tests

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/css/css-syntax
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The 27 pages here are copied byte for byte from `css/css-syntax/` at that commit,
the same WPT commit as `clazel-encoding`'s suite. To update, copy them from a newer
commit, change the commit above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_css_syntax.rs` converts them into
`tests/generated/wpt_css_syntax.rs`. `tests/wpt_table.rs` checks the table; item
5.4's conformance test will run it.

**Most of this suite cannot be run yet.** These are browser tests, so a page only
gives us cases where its checks are literal:

- **Read, 191 calls in 4 pages:** `anb-parsing.html` (67), `anb-serialization.html`
  (20), `input-preprocessing.html` (10) and `urange-parsing.html` (94). Each call of
  the page's own helper becomes a case. A page writes a parse error as the string
  "parse error" or calls `testInvalidUrange`, and either becomes `None`.
- **Not run, 23 pages and 1 test:** the table's `NOT_RUN` lists each with its reason.
  22 compute their checks through the DOM or the CSS object model, `inclusive-ranges.html`
  calls its helpers in loops with computed strings, and `urange-parsing.html` has one
  direct test of `u+a` as a selector. None of these counts as a pass. Pages are not
  all the same size, so 191 is a count of calls, not a share of the suite.

The cases test more than the tokenizer, which item 5.4 must allow for. The expected
results are what a browser's CSS object model serializes, so `2n+1` and `U+A0-AF` are
serializations. `input-preprocessing.html` goes through `selectorText`, so a browser
may replace a lone surrogate before CSS sees it, depending on how that attribute's
string type is converted.

Not vendored, for now:

- `charset/`, 21 pages and their sheets, which need a server sending headers and
  sheets in other encodings. They are evidence for item 5.2's §3.2.
- `missing-semicolon.html`, its reference and `support/missing-semicolon.css`, a
  reftest, which item 5.25 runs.
- `crashtests/`, 3 pages, which need a browser to load them.
- `META.yml` and `WEB_FEATURES.yml`.
