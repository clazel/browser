# WPT reftest references, for the reftest runner (phase-5.md item 5.25)

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The references of the media queries reftests that `clazel-style` vendors
(`crates/clazel-style/tests/data/wpt-mediaqueries/`, the same commit). Each is
copied byte for byte and laid out by its path in the WPT tree, so the runner
(`tests/browse_gpu/reftests.rs`) finds it from the test's `href`:

| WPT path | Bytes | SHA-256 | Its tests |
|---|---|---|---|
| `css/reference/ref-filled-green-100px-square.xht` | 568 | `b7d98bb3f8b7b70e8f76f0b7e99566bc09ca5e5cbae1cef571d7843be87da4f0` | `min-width-001.xht`, `mq-deprecated-001`, `mq-invalid-media-type-001` to `-004` and `-006`, `mq-invalid-media-type-layer-001`, `mq-negative-range-001` and `-002`, `mq-range-001`, `negation-001` and `-002` |
| `css/mediaqueries/reference/ref-green-body.xht` | 434 | `f100f6bfb254cb1c87f0cd05acda00f4c3161d8fd8385c7e86a475a4ac25b0fa` | `relative-units-001` to `-004` |

They were fetched from the raw files at that commit on 2026-11-13, with the
maintainer's approval, by another session, and checked against these hashes
before being copied here.

They are here, not in a crate's `tests/data/`, because nothing converts them:
`tests/data/` holds only the inputs of `xtask`'s converters, and these are read
only by the reftest runner, at run time, as pages to render.

To update: copy the same files from a newer commit, change the commit above and
the hashes in the table.
