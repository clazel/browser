# WPT Opaque Response Blocking tests (Fetch)

Upstream: https://github.com/web-platform-tests/wpt/tree/b64e5b477fe8ddd8c4f94dd27a4de88ab9006ec9
Commit: b64e5b477fe8ddd8c4f94dd27a4de88ab9006ec9
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (flattened into this directory):

| Here | Upstream | Used by `tests/conformance_orb.rs` |
|------|----------|-----------------------------------|
| `img-mime-types-coverage.tentative.sub.html` | `fetch/orb/tentative/` | yes: converted (`cargo xtask testdata`) to its two `Content-Type` lists |
| `img-png-mislabeled-as-html.sub.html`, `...sub-ref.html` | `fetch/orb/tentative/` | yes: the page's meaning is a row |
| `img-png-unlabeled.sub.html`, `...sub-ref.html` | `fetch/orb/tentative/` | yes: the page's meaning is a row |
| `png-mislabeled-as-html.png.headers` | `fetch/orb/resources/` | yes: converted to the mislabeled `Content-Type` |
| `LICENSE.md` | `LICENSE.md` | |

Not copied, and why: the `*.any.js` tests (`fetch()` with script, Phase 7); the
script, media (`status.sub.html`, `hls.html`) and `ping` pages (a media request
has a "no-cors media request state", which the kernel's image and style
requests never have); `compressed-image-sniffing.sub.html` (a gzip response:
the kernel sends no `Accept-Encoding`, decision 6.0(h) A); the binary resources
(the test builds a PNG signature itself).

The coverage page follows the older ORB draft in four rows (it blocks
`application/dash+xml`, `application/vnd.apple.mpegurl`, `audio/mpegurl` and
`text/vtt`; Fetch PR 1755 safelists them). The test says so and expects the
standard's answer.

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.
