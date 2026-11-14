# fontations test fonts, small fonts for `clazel-font`

Upstream: https://github.com/googlefonts/fontations/tree/e5e7f43335e74a605268a8f41c52638c7611ba3b/font-test-data/test_data
Commit: e5e7f43335e74a605268a8f41c52638c7611ba3b
License: MIT (fontations' `LICENSE-MIT`); `TTC.ttc` comes from HarfBuzz, "Old MIT" (both texts in `LICENSE.md`)

Four files are copied from `font-test-data/test_data/` at the commit above,
byte for byte, unmodified:

- `TTC.ttc`: sha256 `a8521588045ed5f1f8b07eecaac06ed3186c644655bfac00dd4507cd316fbdc5` (from `ttc/`; a `ttcf` version 1.0 collection of two faces whose table directories share every table; fontations took it from HarfBuzz's `test/shape/data/in-house/fonts/TTC.ttc`)
- `glyf_components.ttf`: sha256 `54ea04e57233acfb14aaae3aba80b66dbd16da7c3f0ca610432b175b0d3e9d7f` (from `ttf/`; composite glyphs with translations only, a uniform scale, an x and y scale, a two by two matrix, and `SCALED_COMPONENT_OFFSET` against no flag; its source is `ttx/glyf_components.ttx`; `numberOfHMetrics` is 2 of 9 glyphs, so `hmtx` has a `leftSideBearings` array)
- `cmap12_font1.ttf`: sha256 `1134860fcfa1ab18ac0f4020c30b40aa8caf6bf0287dbc3854cceb97b169a34d` (from `ttf/`; a `cmap` with one (3,1) format 12 subtable and no `glyf`)
- `cmap6.ttf`: sha256 `0c6926c4a334201a67377b8d990fe5da4cf6241099e0ddf4e31ae4299db9c9ee` (from `ttf/`; a `cmap` with one (3,1) format 6 subtable and no `glyf`)

`cmap12_font1.ttf` and `cmap6.ttf` hold only `cmap`, `head` and `maxp`, so they
are not faces: the conformance test reads their directory and `cmap` alone.

`xtask/src/testdata/fonts.rs` checks each file's SHA-256 against the lines
above and writes `tests/generated/fonts_fontations.rs`, which embeds them.
