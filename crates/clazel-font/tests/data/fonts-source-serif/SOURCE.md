# Source Serif 4 Regular, a test font for `clazel-font`

Upstream: https://github.com/adobe-fonts/source-serif/tree/80d3f8894c09c937bebfa9011247d2e1c79fd6f4/TTF
Commit: 80d3f8894c09c937bebfa9011247d2e1c79fd6f4
License: SIL Open Font License 1.1, with Reserved Font Name "Source" (`LICENSE.md`, the repository's `LICENSE.md` at that commit, unchanged)

One file is copied from `TTF/` of the `release` branch at the commit above,
byte for byte, unmodified:

- `SourceSerif4-Regular.ttf`: sha256 `e5a4ee6a3d87bb9024796be390c6771e2a0eb1883dae25effaf57ca01668e24b`

What it covers (measured with fontTools 4.55.3 when vendoring): `GPOS` pair
adjustment reached through LookupType 9 extension subtables, in formats 1
and 2, for the `kern` feature under the `DFLT`, `cyrl`, `grek` and `latn`
scripts; `glyf` with 573 composite glyphs and short `loca` offsets
(`indexToLocFormat` 0);
`cmap` formats 4, 6 and 12; no `kern` table and no hinting tables.

OFL 1.1 allows redistribution with software; the font must not be sold by
itself, and a modified version must not use the Reserved Font Name. This file
is not modified.

`xtask/src/testdata/fonts.rs` checks the file's SHA-256 against the line above
and writes `tests/generated/fonts_source_serif.rs`, which embeds it.
