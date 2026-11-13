# WPT `quirks/unitless-length/` and `quirks/hashless-hex-color/`

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/quirks
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The Quirks Mode Standard's two CSS value quirks. Each test is three pages, one per mode
(`quirks.html`, `limited-quirks.html`, `no-quirks.html`), that load the same
`support/common.js`; the copies here keep the test's directory as a prefix
(`unitless-length.common.js`, `unitless-length.quirks.html`). The pages also load
`quirks/support/test-ref-iframe.js`, which only writes a frame in the page's mode and is not
vendored. To update, copy the same files from a newer commit, change the commit above, and
run `cargo xtask testdata`.

`xtask/src/testdata/wpt_quirks.rs` reads `common.js`'s three literal arrays into
`tests/generated/wpt_quirks.rs`: `tests`, each an input and what it must equal in quirks
mode (`q`) and in the other modes (`s`), a missing one meaning the declaration is dropped;
`props`, the properties every input is tried on; and `other_tests`, declarations that must
be dropped in quirks mode. The pages check computed values (`getComputedStyle`) of a test
element against a reference element. Item 5.6 has no computed values yet, so its
conformance test compares the parsed values of the two declarations instead, which is the
same check wherever the two specified values are equal; the differences are listed there.
The SVG half of `hashless-hex-color` (the `fill` attribute) is not run: SVG is not in the
phase.
