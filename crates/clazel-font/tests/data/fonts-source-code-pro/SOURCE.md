# Source Code Pro Regular (CFF), a test font for `clazel-font`

Upstream: https://github.com/adobe-fonts/source-code-pro/tree/803b7e23ec97ae58b6232ea76519a76d428ba268/OTF
Commit: 803b7e23ec97ae58b6232ea76519a76d428ba268
License: SIL Open Font License 1.1, with Reserved Font Name "Source" (`LICENSE.md`, the repository's `LICENSE.md` at that commit, unchanged)

One file is copied from `OTF/` of the `release` branch at the commit above,
byte for byte, unmodified:

- `SourceCodePro-Regular.otf`: sha256 `9f9664e2edf6f045c11e774f9bd0be6993971f2544a39061a5ce478b96b051f8`

What it covers: an `OTTO` font with `CFF ` outlines and no `glyf`. Decision
5.0(c) (C1) takes TrueType outlines only, so this font's table directory is
parsed and the face is reported as unsupported; its `CFF ` table is never
parsed.

OFL 1.1 allows redistribution with software; the font must not be sold by
itself, and a modified version must not use the Reserved Font Name. This file
is not modified.

`xtask/src/testdata/fonts.rs` checks the file's SHA-256 against the line above
and writes `tests/generated/fonts_source_code_pro.rs`, which embeds it.
