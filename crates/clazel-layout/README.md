# clazel-layout

Layout for [Clazel](../../README.md), a web browser whose parsers of untrusted
input carry machine-checked proofs (Phase 5, `docs/phases/phase-5.md`). So far:
font matching (item 5.10, `src/fonts/`) and shaping (item 5.11, `src/shape/`).
The box tree, block, inline and table formatting, white space, line breaking
and the display list (items 5.12 to 5.16) are not started.

Its only dependency is `clazel-font`, which reads every byte of a font.
`rustybuzz` is a dev-dependency, used only by the shaping differential.

## Font matching (item 5.10)

CSS Fonts 3 §5.2 "matching font styles" over a given font table, with the
generic families mapped per OS (decision 5.0(c)), then §5.4's character
handling: the first face in the `font-family` list whose `cmap` maps the
character, then the fallback list, then `.notdef` of the first face.
`src/fonts/mod.rs` lists the modelling choices.

## Shaping (item 5.11)

`shape::Shaper` turns a run of characters in one face into glyphs:

1. each character to one glyph through the face's `cmap` subtable (an
   unmapped character is glyph 0);
2. its `hmtx` advance, or 0 for a combining mark;
3. pair kerning: `GPOS` LookupType 2 for the `kern` feature of the run's
   script, lookup by lookup in LookupList order, or else the `kern` table;
   a mark is skipped when pairs are formed.

The result is in font units (`UnitGlyph`: glyph, cluster, advance, offsets).
`shape::place` scales a run to 26.6 fixed point at the used size with item
5.10's scaling (`clazel_font::outline::scale::scale`), rounding each position
once, half away from zero, so rounding never accumulates along a run. No
hinting.

### Decisions taken for 5.11

Taken from the plan while the maintainer was away; each is also in
`src/shape/mod.rs`.

- **Scope is decision 5.0(c) H1**: `cmap`, `hmtx` and pair kerning, no
  `GSUB`, so no ligatures, though CSS Fonts' default
  `font-variant-ligatures: normal` asks for `liga` (a listed deviation).
- **No `letter-spacing` or `word-spacing`.** The plan includes them "if
  5.0(b) has them". Decision 5.0(b) A is what the exit page needs, and
  "What the exit page needs" lists neither property.
- **Kerning source.** The plan says `GPOS` when the font has `GPOS`, and `kern`
  otherwise. A face whose `GPOS` has no `kern` lookup for the run's script
  (nor for the fallback tables under "Script" below) is kerned from its `kern`
  table. That is the evident intent, and it is what HarfBuzz does. A `GPOS`
  that does not parse counts as absent. Only LookupType 2 is applied: a
  single adjustment that a font puts under `kern` is not (H1 is pair
  kerning; Euphemia UCAS on macOS has one).
- **Where a `GPOS` pair pass resumes**: after the second glyph when its value
  record is non-zero, else at it (HarfBuzz's reading: the chapter is silent;
  HarfBuzz tests `valueFormat2`, which `clazel-font` does not expose).
- **Marks**: a character in the combining-mark blocks of Latin, Greek and
  Cyrillic (U+0300–036F, U+0483–0489, U+1AB0–1AFF, U+1DC0–1DFF,
  U+20D0–20FF, U+2DE0–2DFF, Cyrillic Extended-B's marks, U+FE20–FE2F) has
  zero advance and is placed at the pen after its base. There is no `mark`
  feature, no `GDEF`, and kern pairs skip marks as if every lookup had
  `IGNORE_MARKS`.
- **The `kern` table's value goes to the first glyph's advance.**
  HarfBuzz splits it between the two glyphs instead, which puts every glyph
  in the same place.
- **Script**: the first character of the run in a Latin, Greek or Cyrillic
  block picks `latn`, `grek` or `cyrl`, else `DFLT`. The `GPOS` script
  table is that script's or `DFLT`, and if neither has a `kern` lookup,
  `dflt` and then `latn`, as HarfBuzz tries them. With this, a run of
  punctuation in PT Sans is kerned as HarfBuzz kerns it. HarfBuzz stops at
  the first listed table even when it has no `kern` feature.
  `clazel-font` does not say whether a script is listed, so we go on to the
  next table (listed).
- **Right-to-left runs stay in logical order** (no UAX #9, Phase 8). There is
  no Unicode normalization, no handling of default-ignorable characters and no
  space fallback.
- **Positions in 26.6**: a glyph's origin is its pen position plus its offset,
  scaled. Its advance is the difference of the scaled pen positions after and
  before it. A value outside `i32` is clamped. A negative size gives zeros.
- **Every failure degrades**, and nothing panics: an unreadable `cmap` gives
  glyph 0, an unreadable advance is 0, and an unreadable pair is not adjusted.
- **Target tier stays 0**, as the plan's Crates table gives for this crate.
  The shaper still has Kani harnesses for its arithmetic and indexing (below),
  as the item asked.

## Verification

Tier: `tier = 0`, `target-tier = 0` in `Cargo.toml` (the plan's Crates table).

Unit tests: `src/fonts/` per CSS Fonts rule; `src/shape/tests.rs` from the
`gpos` chapter's pair kerning examples (Example 4, PairPosFormat1 "Po"/"To";
Example 5, PairPosFormat2 lowercase before punctuation), each wrapped in a
minimal `GPOS` table and run through the kerning pass, plus the resume rule,
mark skipping and the `kern` table.

Kani harnesses (`src/shape/proofs.rs`) for the shaper's arithmetic and
indexing: no panic, no arithmetic overflow and no index out of bounds, on every
input within these bounds, with every loop's unwinding checked. Measured
locally, one harness at a time with `cargo kani -p clazel-layout --harness …
--exact`, on an Apple-silicon Mac while a Miri run used one other core. Times
are wall clock, including cargo's start. Memory is the peak resident set
size of the run, CBMC included.

| Harness | Inputs | Time | Peak memory |
|---------|--------|------|-------------|
| `pen_any` | the pen's accumulation and clamping on any pen (`i64`) and advance | 1.2 s | 0.15 GB |
| `to_26_6_any` | font units to 26.6 for any value, any size and any `unitsPerEm`; 0 for a negative size or zero `unitsPerEm`; the sign kept | 1.9 s | 0.16 GB |
| `place_step_any` | one glyph placed from any pen position, any glyph, any size and `unitsPerEm` (the body of `place`'s loop for every run length) | 5.8 s | 0.55 GB |
| `place_any_2` | whole runs of up to 2 glyphs, any values, any size and `unitsPerEm` | 23.4 s | 1.67 GB |
| `add_value_any` | any ValueRecord added to any glyph | 1.0 s | 0.15 GB |
| `next_base_any_6` | the next non-mark glyph after any index in any run of up to 6 glyphs is inside the run, after the index, and not a mark | 3.5 s | 0.20 GB |
| `kern_pass_any_4` | the `kern` table pass on any run of up to 4 glyphs with any value for every pair; it terminates | 9.0 s | 1.07 GB |
| `pair_pass_any_4` | the `GPOS` pair pass on any run of up to 4 glyphs with any answer (none, or any two ValueRecords) for every pair; it terminates | 29.9 s | 4.21 GB |

**Not covered by Kani**: reading the face (`cmap`, `hmtx`, `GPOS`, `kern`
are `clazel-font`'s, with that crate's harnesses; the passes here take the
pair lookups as arbitrary answers); `Shaper::glyphs`, which iterates a `&str`
and calls the face and has no arithmetic of its own; and runs longer than
the bounds above. Those are covered by the unit and differential tests.
CI has not run these harnesses yet.

`tests/conformance_shaping.rs` compares the shaper with `rustybuzz` 0.20.1
(HarfBuzz's algorithm in Rust). `rustybuzz` runs with the `kern` feature on and
every other feature it would apply turned off (`liga` among them), left to
right, at cluster level `Characters`, with the script our shaper chose. The
texts are Latin, Greek and Cyrillic sentences (including combining marks),
every ordered pair of characters from an alphabet per script, and every
triple from twelve Latin characters that kern: 22,830 texts per face. For
each glyph the test compares, in font units, the glyph id, the cluster and the
advance, and the offsets of every glyph that is not a mark.

| Suite | Cases | Agree | Expected differences | Failures |
|-------|-------|-------|----------------------|----------|
| vendored fonts (5 TrueType faces; the CFF face is skipped) | 114,150 | 114,147 | 3 | 0 |
| system fonts (this Mac: 406 files, 666 faces, every 11th case) | 1,382,253 | 1,361,817 | 20,436 | 0 |

The vendored expected differences are 2 `canonical composition` and 1
`unmapped character`. On the system fonts: 6,873 `unmapped character`, 6,800
`AAT tables`, 6,665 `kern table split`, 49 `GDEF mark classes`, 31
`canonical composition`, 15 `non-pair lookups under kern`, 3 `marks in kern
pairs`. The top of the test file explains each one. Under Miri the vendored
suite runs every 1,000th case: 115 cases, all agreeing, in 46 s on Miri's
clock. The system suite opens files, so it is ignored under Miri. Natively
the vendored suite takes 4 s and the system suite 65 s.
