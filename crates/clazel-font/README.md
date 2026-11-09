# clazel-font

OpenType font files and the TrueType tables a face needs, for
[Clazel](../../README.md), a web browser whose parsers of untrusted input carry
machine-checked proofs. Phase 5 item 5.9 (`docs/phases/phase-5.md`).

Every byte of a font is read by this crate's own code: it has no dependencies.
`ttf-parser` and `read-fonts` are dev-dependencies, used only by the
differential test.

## What it reads

Pinned to the **OpenType specification version 1.9** (Microsoft), with
**Apple's TrueType Reference Manual** as the second text; `src/lib.rs` lists
the modelling choices.

- The table directory (`sfntVersion` `0x00010000`, `OTTO` or Apple's `true`),
  table records, checksums (reported, never enforced), and `ttcf` collections.
- `head`, `hhea`, `maxp`, `hmtx`, `loca`.
- `glyf`: simple glyphs (flag repeats, short vectors) decoded one point at a
  time; composite glyphs with offsets or point matching and all three scale
  forms; flattening to quadratic contours within stated bounds (component
  depth 8, 1,024 components, 65,536 points).
- `cmap` formats 0, 4, 6 and 12, one Unicode subtable per face.
- `name` (UTF-16BE records), `OS/2`, `post` (header).
- `kern` version 0, format 0.
- `GPOS` LookupType 2 (formats 1 and 2) and 9, with ScriptList, FeatureList,
  LookupList, Coverage and ClassDef formats 1 and 2 and ValueRecord, for the
  `kern` feature.

Not read (decision 5.0(c)): `CFF `/`CFF2` (a CFF face is reported
unsupported), `GSUB`, `GDEF`, variations, colour and bitmap tables, and every
instruction table: no bytecode ever runs on font bytes.

## Verification

Tier: `tier = 0`, `target-tier = 1` in `Cargo.toml`. The tier is raised only
after CI's full verification has run the harnesses below green.

Kani harnesses (`src/proofs.rs`): no panic, no arithmetic overflow and no read
outside a slice, on every input within these bounds, with every loop's
unwinding checked:

| Harness | Inputs |
|---------|--------|
| `read_any_8` | the readers on every byte string of up to 8 bytes, any offset and length |
| `directory_any_44` | the directory and collection header on every file of up to 44 bytes, any face index and record, with checksums |
| `directory_offsets_4k` | a directory at any offset of any 4 KiB file, any record; a collection header and any face |
| `fixed_tables_any_104` | `head`, `hhea`, `maxp`, `post`, `OS/2` on every table of up to 104 bytes |
| `hmtx_any_counts_4k` | `hmtx` on every table of up to 4 KiB, any counts, any glyph |
| `loca_any_4k` | `loca` on every table of up to 4 KiB, either format, any glyph count and glyph |
| `glyf_point_step` | one step of the point decoder from any state over any 64 bytes (the loop body for every point) |
| `glyf_glyph_any_14` | every glyph of up to 14 bytes: header, flag walk, first 4 points, contour ends, component records |
| `glyf_transform_any` | a component transform on any matrix and point |
| `outline_loca_glyf` | any short `loca` of 3 glyphs with any `glyf` of up to 12 bytes, any glyph index, flattened with limits depth 1, 2 components, 2 points |
| `cmap_any_28` | `cmap` on every table of up to 28 bytes: choice, lookup of any character, ranges, order |
| `cmap_lookup_512` | format 4 and 12 lookups of any character in any 512-byte subtable |
| `name_any_16` | `name` on every table of up to 16 bytes, any record, any name ID |
| `name_decode_any_8` | UTF-16BE decoding of every byte string of up to 8 bytes |
| `kern_any_40` | `kern` on every table of up to 40 bytes, any pair |
| `kern_lookup_512` | a format 0 lookup of any pair in any 512-byte table |
| `coverage_class_def_512` | Coverage and ClassDef lookups of any glyph in any 512-byte table |
| `pair_pos_512` | a PairPos subtable of either format, any pair, in any 512-byte subtable |
| `gpos_kern_lookups_any_16` | `GPOS` on every table of up to 16 bytes: `kern` lookups of any script |
| `gpos_pair_adjustment_any_16` | `GPOS` on every table of up to 16 bytes: pair adjustment of any lookup and pair |
| `face_any_24` | `Face::parse` on every file of up to 24 bytes |

The limits of the bounds are stated in `src/proofs.rs`: whole simple glyphs
are bounded by their first 4 points (the per-step harness covers the rest),
flattening uses smaller limits than the shipped ones (the same code), and no
24-byte file is a whole face.

Unit tests transcribe the worked examples of the chapters: the `cmap` format
4 example, `chapter2` Examples 5 to 8 (Coverage and ClassDef) and `gpos`
Examples 4 and 5 (PairPos formats 1 and 2). Three errata found in the text
are in `docs/ERRATA.md`.

`tests/conformance_fonts.rs` compares the crate with `ttf-parser` and
`read-fonts` on every vendored font, every system font and 10,000 mutated
fonts; its expected differences are listed with reasons at the top of the
file.

## Test fonts

Under `tests/data/`, each with its `SOURCE.md` (upstream, commit or archive
hash, per-file SHA-256) and licence: DejaVu Serif 2.37, Source Serif 4,
Source Code Pro (CFF), and four small files from fontations' test data.
