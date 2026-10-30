# WPT `encoding/`, labels, single-byte and UTF-16 cases

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/encoding
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The commit is the one the repository already pins for WPT (item 3.3 and
`../wpt-encoding/`). Files, copied byte for byte from `encoding/` at that
commit, with their SHA-256:

| File here | Upstream path | SHA-256 |
|-----------|---------------|---------|
| `encodings.js` | `encoding/resources/encodings.js` | 1742a28bafab3e3de2fa4a394366af3796d45c46587a51ba98e4fa90ca64ea64 |
| `single-byte-decoder.js` | `encoding/resources/single-byte-decoder.js` | c37feb2d219bd28e72f02d8559f55d1315d81b627371f2af797d117c606cc081 |
| `single-byte-decoder.any.js` | `encoding/single-byte-decoder.any.js` | 14b14ebdb501e03f2c0833514d0d4da9e7132548537beb22e577aedda75f9ae6 |
| `textdecoder-fatal-single-byte.any.js` | `encoding/textdecoder-fatal-single-byte.any.js` | a4c8f7664ccf35a7192e813341f591216e46dad696d113252364df050038dd8e |
| `textdecoder-labels.any.js` | `encoding/textdecoder-labels.any.js` | be155d59592f430d7fcc0827d64a0c39e00a56e8c83323127178e6e18113654f |
| `textdecoder-utf16-surrogates.any.js` | `encoding/textdecoder-utf16-surrogates.any.js` | f04fabfe9a6fe3f24eb66e4967637cb73b6b874a33bd5214d27af1d38ed17f3f |
| `LICENSE.md` | `LICENSE.md` (repository root) | 5fac07febb0e2a97fb0d7b0def149ec08b642e1ba4b9c345283ab1cbd2af6570 |

The two `resources/` files are renamed to their base names because a suite
directory is flat. Phase 4's plan (item 4.1) names
`single-byte-decoder.window.js`; at this commit the test is
`single-byte-decoder.any.js` (its `TextDecoder` variant is what is
converted). To update, copy the same files from a newer commit, change the
commit above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_encoding_legacy.rs` converts them into
`tests/generated/wpt_encoding_legacy.rs`, read by
`tests/conformance_labels.rs` and `tests/conformance_legacy.rs`. It reads
only literals in fixed places, and checks that the code computing each
test's expectations is the text it expects, so an update that reshapes a
file fails the conversion instead of dropping cases.

What is converted:

| File | Cases |
|------|-------|
| `encodings.js`, `textdecoder-labels.any.js` | every label: as given, upper-cased, and with each whitespace character before, after and around it, names its encoding ("get an encoding"). The test skips replacement's labels, which the conformance test checks too but does not count as WPT cases |
| `single-byte-decoder.js`, `single-byte-decoder.any.js` | every label of every single-byte encoding: decoding bytes 0 to 254 gives the encoding and the code points of WPT's own copy of the index |
| `textdecoder-fatal-single-byte.any.js` | every byte 0 to 255 of every single-byte encoding: fatal decoding fails exactly on the listed bytes |
| `textdecoder-utf16-surrogates.any.js` | each case: replacement decoding gives the expected string, fatal decoding fails |

Not converted, and why:

- The `XMLHttpRequest` variant of `single-byte-decoder.any.js`: it fetches
  `resources/single-byte-raw.py` from a server and decodes the same bytes
  through XHR; the bytes and expectations are those of the `TextDecoder`
  variant.
- `legacy-mb-*/`: the multi-byte decoders are item 4.4, which may slip to
  Phase 8 (item 4.0(b)); their suites are vendored with that item.
- `replacement-encodings.any.js`, `api-replacement-encodings.any.js`: they
  test `TextDecoder` rejecting the replacement encoding and an HTML
  document decoded with it; the replacement decoder's behaviour is
  covered by its spec's examples and the `encoding_rs` differential.
