# html5lib-tests `encoding/`: every encoding sniffing case

Upstream: https://github.com/html5lib/html5lib-tests/tree/c777c408b61078ea2eb4acefc2535f54dbc8b28a/encoding
Commit: c777c408b61078ea2eb4acefc2535f54dbc8b28a
Date: 2026-10-01 (the commit `../html5lib-tokenizer/` pins)
License: MIT (`LICENSE.md`, copied from `LICENSE` at the root of the repository at that commit)

Files, copied byte for byte from `encoding/` at that commit, with their
SHA-256:

| File here | Upstream path | SHA-256 |
|-----------|---------------|---------|
| `tests1.dat` | `encoding/tests1.dat` | ef54dd3d9c256a6830c266808c0277545a156a241b350c613c996a4cea52e5f7 |
| `tests2.dat` | `encoding/tests2.dat` | 5e00d81e6207307f1186ea85f85b5f58003af94f5a7c6a3e06ca19c17567f51b |
| `test-yahoo-jp.dat` | `encoding/test-yahoo-jp.dat` | dc353a7ceaa9428a668e7846e78efd18f7e0a09e768d6be61166c12fc223a432 |
| `scripted-tests1.dat` | `encoding/scripted/tests1.dat` | a6ee1080bf863b71163a3213c4b01ca8dabdf2521a2ed00e74348ace8dd13c50 |
| `LICENSE.md` (from `LICENSE`) | `LICENSE` | ff512aac9ef231d504be5afaf4429005024e4b2aaf257be39524f37b8402aaf2 |

`scripted/tests1.dat` is renamed because a suite directory is flat. To
update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/html5lib_encoding.rs` converts the cases into
`tests/generated/html5lib_encoding.rs`, read by `tests/conformance_sniff.rs`:
each case is its input bytes (the lines between `#data` and `#encoding`)
and the expected encoding's name, and runs through HTML §13.2.3.2 "the
encoding sniffing algorithm" with no transport encoding. Each case is one
HTML document's first bytes, so its expected encoding is what the whole
algorithm returns, prescan and default (windows-1252) included.

Not converted, and why:

- `scripted/tests1.dat`'s one case writes its `<meta>` with
  `document.write`, which needs a script; this phase runs none. It is
  converted to a count of cases not run, never to passes.
- `chardet/test_big5.txt`: a sample text for encoding *detection*
  (frequency analysis, step 8 of the algorithm, which this implementation
  does not do), with no expected result in html5lib-tests' format.
