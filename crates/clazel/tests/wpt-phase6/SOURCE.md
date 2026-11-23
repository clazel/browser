# WPT files shared by Phase 6's forms and image items (phase-6.md item 6.1)

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The same WPT commit as `clazel-css`'s and `clazel-encoding`'s suites. Files are
copied byte for byte (taken with `git archive`, so line endings are the
repository's, not a Windows checkout's) from these paths:

- `html/semantics/forms/form-submission-0/`, `the-form-element/`,
  `the-input-element/`, `the-button-element/`, `the-select-element/`,
  `the-textarea-element/`, `the-option-element/`, `the-optgroup-element/`,
  `resetting-a-form/`, `attributes-common-to-form-controls/`,
  `form-control-infrastructure/`
- `html/semantics/embedded-content/the-img-element/`
- `url/urlencoded-parser.any.js`
- `LICENSE.md`

Left out on purpose: the rest of `html/semantics/forms/` (nested browsing
contexts, validation UI, selection APIs, script-only features), and four files
that hold carriage returns (`multiline-placeholder-cr.html` and
`multiline-placeholder-crlf.html` in each of `the-input-element/` and
`the-textarea-element/`), which the repository's
`eol=lf` rule would rewrite. Resources the pages load from outside these
directories (`/common/`, `/images/`, `/resources/`) are not here.

`MANIFEST.sha256` lists the SHA-256 of every other file here (`sha256sum -c
MANIFEST.sha256` from this directory).

These are browser tests: most pages need script. Nothing converts or reads
them yet; the Phase 6 item that uses a part (6.10, 6.11, 6.13, 6.14) writes its
converter in `xtask/src/testdata/` and picks the script-free cases.

To update, copy the same paths from a newer commit, change the commit above and
regenerate `MANIFEST.sha256`.
