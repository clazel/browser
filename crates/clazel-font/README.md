# clazel-font

OpenType font files and the TrueType tables a face needs, for
[Clazel](../../README.md), a web browser whose parsers of untrusted input carry
machine-checked proofs. Phase 5 items 5.9 (font tables) and 5.10 (glyph
outlines as paths; `docs/phases/phase-5.md`).

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

## Outlines (item 5.10)

`src/outline/` turns a flattened glyph into a `Path`: closed contours of
on-curve and off-curve points in 26.6 fixed-point pixels at a given size,
every implied on-curve point between two off-curve points made explicit and
each contour starting on-curve, so a contour reads as lines and quadratic
Béziers. `Path` is the input of the glyph rasterizer (`clazel-glyph-mask`,
item 5.17), which takes it from this crate. A glyph that cannot be read or
flattened, or whose scaled coordinates leave `i32`, is an empty path; the
modelling choices are listed in `src/outline/mod.rs`.

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
| `glyf_glyph_any_20` | every glyph of up to 20 bytes: header, contour ends, the flag walk, any contour end, the first point or component |
| `glyf_component_step` | one component record from any state over any 20 bytes (the loop body for every component) |
| `glyf_transform_any` | a component transform on any matrix and point |
| `cmap_any_28` | `cmap` on every table of up to 28 bytes: records and the subtable choice |
| `cmap_subtable_any_24` | a lookup of any character in every subtable of up to 24 bytes |
| `cmap_ranges_any_24` | the ranges of every subtable of up to 24 bytes |
| `cmap_order_any_24` | the order check on every subtable of up to 24 bytes |
| `cmap_lookup_128` | format 4, 6 and 12 lookups of any character in any 128-byte subtable |
| `name_decode_any_8` | UTF-16BE decoding of every byte string of up to 8 bytes |
| `kern_any_32` | `kern` on every table of up to 32 bytes, any pair |
| `kern_lookup_128` | a format 0 lookup of any pair in any 128-byte table |
| `coverage_class_def_128` | Coverage and ClassDef lookups of any glyph in any 128-byte table |
| `pair_pos_48` | a PairPos subtable of either format, any pair, in any 48-byte subtable |
| `outline_scale_any` | font units to 26.6 for any coordinate, any size and any `unitsPerEm`; a result only for a size ≥ 0 and `unitsPerEm` > 0 |
| `outline_midpoint_any` | the implied point between any two coordinates lies between them |
| `outline_contour_start` | a contour's start from any first and last point is on-curve, and is the first (or last) point when that is on-curve |
| `outline_contour_step` | one step of the contour conversion from any previous and next point: no two consecutive off-curve points (the loop body for every contour length) |

Whole glyphs are checked to their first point or component; the per-step
harnesses cover the point decoder's and the component reader's loop bodies
from any state.

**Not done.** These harnesses do not finish locally, even at very small
bounds: they time out after 40 minutes or exhaust memory. They are not in the
crate, and their code is covered only by unit tests and the differential:

- `loca` with `glyf` flattened to an outline;
- a `name` lookup that decodes the chosen record;
- `GPOS` from the table header (`kern` lookups and pair adjustment);
- `Face::parse`;
- item 5.10's whole-contour and whole-path conversions (`push_contour` on 2
  points, `path_from_outline` on 2 points in 2 contours): past 20 minutes
  each, and out of memory at 10 GB on 4 points. The start and step
  harnesses above give well-formedness for every contour length by
  induction over the loop; the differential test checks every glyph's path.

Each table that `Face::parse` reads, a PairPos subtable, Coverage and ClassDef,
and the UTF-16BE decoder have their own harnesses. Item 5.9's
"`loca` with `glyf` on symbolic glyph indices" is therefore covered only for
`loca` alone and for glyph descriptions, not for flattening.

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
