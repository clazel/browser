# clazel-glyph-mask

Glyph outlines to 8-bit coverage masks, for [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs. Phase 5
item 5.17 (`docs/phases/phase-5.md`). It runs in the renderer: the GPU process
draws rectangles and textured quads, so glyph shapes become masks here and font
bytes never reach the GPU process, only masks. No surface and no blending.

Its only dependency is `clazel-font`, for item 5.10's path type.
`ab_glyph_rasterizer` is a dev-dependency, used only by the differential test.

The crate was named `clazel-raster` in the plan; the maintainer renamed it,
because the roadmap's later raster image decoders (PNG, JPEG, GIF, WebP) would
be confused with it.

## What it does

`glyph_mask(path, offset)` takes a `clazel_font::outline::Path` (closed
contours of lines and quadratic Béziers in 26.6 fixed point, y up, as
`clazel-font`'s `outline/` produces them) and a quarter-pixel offset, and
returns a `Mask`: width, height, its position relative to the glyph origin in
screen pixels (y down), and one coverage byte per pixel, row after row.

1. **Place** (`src/place.rs`): the mask is the path's control box after the
   offset, rounded out to whole pixels; points move to mask units (2⁻¹⁴ px).
2. **Walk** (`src/segments.rs`): each contour as lines and Béziers, per the
   `glyf` chapter; any contour is accepted, well formed or not.
3. **Flatten** (`src/flatten.rs`): each Bézier cut into the least power of
   two of equal parameter pieces whose error bound is 15/64 px (a power of
   two so that the division is a shift), points exact in integers and
   rounded, so the polyline is within a quarter pixel of the curve.
4. **Accumulate** (`src/accumulate.rs`): each line cut at every row and
   column edge, the exact signed area of each piece added to its cell and the
   next, running sums per row, magnitude clamped to one cell and scaled to
   0..=255.

## Decisions

Taken from the plan (item 5.17's "listed choices", decision 5.0(d), the exit
criteria and the verification tiers), and recorded here as the plan asks:

- **CPU masks in the renderer.** 5.0(d) as the plan now stands: the GPU
  draws, and glyph masks are still made on the CPU in the renderer.
- **Input type**: item 5.10's `Path`, taken from `clazel-font` (5.10 put
  the type there so this crate could start with it alone).
- **Quarter-pixel offset**: 0, ¼, ½ or ¾ px in each of x and y (`Offset`,
  `Quarter`), so subpixel pen positions need four masks per axis.
- **Non-zero rule by clamping**: coverage is the magnitude of the signed
  area clamped to [0, 1], which equals non-zero winding except where
  contours overlap with opposite orientation (as the plan states). Taking
  the magnitude lets either orientation paint.
- **Flattening tolerance**: within a quarter pixel (15/64 px plus rounding),
  with a power of two of pieces per Bézier, at most 128.
- **Fixed point throughout**, no floating point, so a Kani harness models
  the arithmetic exactly where it reaches; every step is checked and returns `Error::Overflow`
  rather than panicking.
- **Maximum mask**: 1024 × 1024 pixels (`MAX_SIDE`); a larger glyph is
  `Error::TooLarge` and draws nothing (for the hostile pages of 5.26).
- **Maximum complexity**: 65,536 lines after flattening (`MAX_LINES`), else
  `Error::TooComplex`; it bounds the work per glyph and keeps every cell
  within 2⁴⁷.
- **Rounding**: `round(min(|area|, 1) × 255)`, half up.
- **Tier**: 0 now, target 1 (`Cargo.toml`), per the plan's Crates table and
  exit criterion 1. The tier is raised only after CI's full verification has
  run the harnesses below green.

## Verification

Tier: `tier = 0`, `target-tier = 1` in `Cargo.toml`.

Kani harnesses (`src/proofs.rs`): no panic, no arithmetic overflow and no
index out of bounds on every input within these bounds, every loop's unwinding
checked, and no `Error::Overflow`. Each was run alone on an Apple-silicon Mac
with Kani 0.68.0 and CBMC 6.11.0, capped at 20 minutes and 8 GB; time is
Kani's verification time, memory the run's peak resident size.

| Harness | Inputs | Time | Peak memory |
|---------|--------|------|-------------|
| `place_screen_any` | screen coordinates of any `i32` point at any offset | 0.1 s | 140 MB |
| `place_box_any` | the pixel box of any control box from `i32` points at any offset, mask up to 1024: holds every point and fits, else `TooLarge` | 0.7 s | 146 MB |
| `place_local_any` | any point in a box of up to 1024 px lands in the mask | 0.3 s | 141 MB |
| `segments_any_3` | the walk of any contour of up to 3 points in a 1024-px mask, any flags: every point stays in the mask | 8.2 s | 725 MB |
| `pieces_any` | the piece count of any Bézier in a 1024-px mask: a power of two up to 128 meeting the tolerance | 1.2 s | 147 MB |
| `point_any_2` | `B(1/2)` of any Bézier in a 1024-px mask lies in its control box | 1.3 s | 150 MB |
| `point_any_4` | `B(i/4)`, i = 1, 2, 3, likewise | 42 s | 229 MB |
| `cell_any_1x1` | one cell update (x offsets 0..=1 px, height −1..=1 px) in any state of a 1 × 1 mask with cells within ±2⁵⁰: no cell moves by more than 2³¹ | 3.2 s | 310 MB |
| `finish_row_any_6` | the finishing pass on any row of up to 6 pixels with cells within ±2⁵⁰ | 5.7 s | 485 MB |
| `coverage_any` | any running sum to a coverage in 0..=255, 255 from a full cell | 0.1 s | 144 MB |

A cell starts at 0 and one line moves it by at most 2³¹, so 65,536 lines
(`MAX_LINES`) keep it within 2⁴⁷ < 2⁵⁰, which the cell and finishing
harnesses assume.

**Not covered by a harness.** These ran past the 20-minute cap or the 8 GB
cap and are not in the crate; symbolic 64-bit multiplication and division are
what CBMC cannot finish here. Each is covered by unit tests, by the
differential test below, and by a written bound in `src/proofs.rs`; every
step is checked, so a missed case returns `Error::Overflow`, never a panic or
a wrapped value.

- A line's loops and its `x_at`/`y_at` division: `x_at` alone in a 1024-px
  mask ran past 20 minutes; a whole line in a 1 × 1 mask passed 8 GB in 88 s.
- A cell update in a mask larger than 1 × 1: a symbolic size up to 4 × 4
  passed 8 GB in 38 s.
- The placement loop over a path's points: one point ran past 20 minutes
  (three points made a 2.6-million-step program).
- The whole pipeline on any path, which contains all of the above. So the
  plan's "for every path up to a stated number of segments … flattening and
  accumulation never panic, overflow or index out of bounds" holds by the
  harnesses above only step by step, not for a whole path.
- `B(i/n)` for 8 to 128 pieces: every pair up to 8 pieces ran past 20
  minutes, with the pairs concrete and with them symbolic.

Unit tests cover each primitive: placement, the contour walk (well-formed and
malformed contours), piece counts and curve points (each polyline measured
within ¼ px of the exact curve), cells, rows, coverage rounding, overlaps and
holes, offsets, and the error cases. Under Miri they take 6.9 s in all.

## Differential test

`tests/conformance_masks.rs` draws every glyph of every vendored font
(`clazel-font`'s `tests/data/`: DejaVu Serif, Source Serif 4, the small
fontations files; Source Code Pro is CFF and has no glyphs here) at every
size from 8 to 72 px, the offset cycling through all sixteen quarter-pixel
offsets: 325,845 masks, the largest 159 × 97 px. Against
`ab_glyph_rasterizer` 0.1.10:

- **Same lines** (the plan's check: within one coverage level per pixel):
  it accumulates our flattened lines. All 325,845 masks pass. Pixels by
  difference: 259,578,821 equal, 377,705 one level apart, none more.
- **Own curves**: it flattens the Béziers itself (within about 0.14 px).
  All 325,845 masks are within the stated bound of 142 levels (two
  polylines within ¼ px and 0.144 px of the curve, over a pixel's diagonal);
  the largest difference is 57 levels. The full histogram is printed by the
  test.

The reference draws with a one-pixel left margin: its `draw_line` skips a
row piece whose left end rounds to just below x = 0 in row 0, and its running
sum carries the loss through the rest of the mask. Before the margin two masks
differed by up to 124 levels; ours matched the exact polygon area there and
the reference's did not (the test's doc comment has the numbers).

Under Miri the test draws only masks up to 64 × 64, every 17,011th (glyph,
size) pair (19 masks), 78 s on Miri's clock.
