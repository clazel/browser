# DejaVu Serif 2.37, a test font for `clazel-font`

Upstream: https://github.com/dejavu-fonts/dejavu-fonts/releases/download/version_2_37/dejavu-fonts-ttf-2.37.tar.bz2
SHA-256: fa9ca4d13871dd122f61258a80d01751d603b4d3ee14095d65453b4e846e17d7
License: Bitstream Vera Fonts licence with DejaVu's changes in the public domain, and the Arev Fonts licence for glyphs imported from Arev (`LICENSE.md`, the archive's `LICENSE` file, unchanged)

The release archive (tag `version_2_37`, commit
`0eda8a319c08835009849583cd090bb5b141ce25`; the repository holds only the
sources, so the archive is what is pinned) has the SHA-256 above. One file is
copied from its `ttf/` directory byte for byte, unmodified, and `LICENSE.md` is
the archive's `LICENSE`:

- `DejaVuSerif.ttf`: sha256 `42d1edeb7952f31b1f96d767ed7030b08a39e0c372b0071641518864e2bffb51`

What it covers (measured with fontTools 4.55.3 when vendoring): `glyf`
outlines with 1,407 composite glyphs and long `loca` offsets
(`indexToLocFormat` 1); `cmap` subtables (0,3) format 4,
(0,10) format 12, (1,0) format 6, (3,1) format 4 and (3,10) format 12; a
`kern` table, version 0 with one format 0 subtable of 1,367 pairs; and `GPOS`
pair adjustment (LookupType 2) in format 2, with `name`, `OS/2` and `post`.

The licence allows redistribution and bundling with software; a modified
font must not use "Bitstream" or "Vera" in its name. This file is not
modified. DejaVu is the family proposed as the bundled fallback (5.0(c)); that
is not decided here, and no binary includes this file.

`xtask/src/testdata/fonts.rs` checks the file's SHA-256 against the line above
and its first four bytes against the `sfntVersion` values, and writes
`tests/generated/fonts_dejavu.rs`, a table that embeds it with
`include_bytes!`. `tests/conformance_fonts.rs` reads that table.
