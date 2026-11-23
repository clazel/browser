# WPT form encoding tests (URL and HTML form submission)

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (they are the same files item
6.1 vendored under `crates/clazel/tests/wpt-phase6/`; copied here so that a
change to them is seen by `cargo xtask verify --changed` for this crate):

| Here | Upstream |
|------|----------|
| `urlencoded-parser.any.js` | `url/urlencoded-parser.any.js` |
| `urlencoded2.window.js` | `html/semantics/forms/form-submission-0/urlencoded2.window.js` |
| `text-plain.window.js` | `html/semantics/forms/form-submission-0/text-plain.window.js` |
| `multipart-formdata.window.js` | `html/semantics/forms/form-submission-0/multipart-formdata.window.js` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_form_encodings.rs` converts them into
`tests/generated/wpt_form_encodings.rs`, read by
`tests/conformance_encodings.rs`. The `formTest(...)` pages submit a form
into a frame (needs script); the converter reads each call's `name`,
`value`, `formEncoding` and `expected`, and the test runs the same form
through the proven `submit_exec`. Calls whose value is a `File` need a file
input (out, phase-6.md 6.0) and are counted, not run. The page's helper
`enctypes-helper.js` is not vendored: the converter checks the three
`formSubmissionTemplate(...)` lines that say which enctype each file tests.
`urlencoded-parser.any.js` parses `input` into pairs; the test runs the
serializer on the pairs and parses its output back (a round trip).
