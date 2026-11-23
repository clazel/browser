# clazel-svg

Static SVG for [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs. Phase 6 item 6.11a
(`docs/phases/phase-6.md`). It runs in the renderer's sandbox, on bytes a
page chose, and implements the one interface of every Phase 6 decoder,
`clazel_image_shape::Decoder` (item 6.3).

Its only dependency is `clazel-image-shape`. `tiny-skia` is a
dev-dependency, used only by the differential test. No XML or SVG library
is used: the tokenizer is ours (CLAUDE.md rule 8).

## Scope: exactly the two files Hacker News uses

The decoder reads `y18.svg` (the logo) and `triangle.svg` (the vote arrow),
which 6.1's inventory found on HN's pages, and **nothing else**:

- elements `svg` and `path`;
- attributes `xmlns`, `width`, `height`, `viewBox` (on `svg`), `d`, `fill`
  (on `path`);
- path commands `M`/`m`, `L`/`l`, `H`/`h`, `V`/`v`, `Z`/`z`, with the
  implicit `lineto` after a `moveto`, numbers as decimal fractions;
- `fill` as `#rgb` or `#rrggbb`; the non-zero fill rule; the default
  `preserveAspectRatio` (`xMidYMid meet`); the XML declaration and
  comments skipped.

Anything else (another element, attribute, path command or colour syntax,
`style`, entities, `DOCTYPE`, `CDATA`, a namespace prefix, text) is an
`Error`, so the image is a broken image showing its `alt` (decision
6.0(c)'s S1), **never a partial draw**: the document is read twice, a
validating pass and then a drawing pass, and only a document that passes
the first is drawn. **Wikipedia's SVGs need what this does not have**
(gradients, `g`, `circle`, `clipPath`, `defs`, `transform`, `style`,
curves, metadata) and show as broken images. Phase 8 does SVG in full.

`triangle.svg` is `width="32" height="32"` with `viewBox="0 0 32 16"`: its
intrinsic size is 32 by 32, not 32 by 16 as the plan's text reads, and at
`background-size: 10px` it is drawn 10 by 10. The content is clipped to the
image, not to the `viewBox` (listed choice 5 in `src/lib.rs`).

| File | Holds |
|------|-------|
| `src/lib.rs` | the pinned standards, the section numbers, the eleven listed choices |
| `src/xml.rs` | the tokenizer (XML 1.0: prolog, comments, tags, attributes) |
| `src/num.rs` | numbers (SVG 2 9.3.9) in fixed point |
| `src/path.rs` | path data (9.3) to the edges of a polygon |
| `src/paint.rs` | `fill` |
| `src/map.rs` | the viewport transform (SVG 2 8.2, `xMidYMid meet`) |
| `src/raster.rs` | the rasterizer: non-zero fill, 16 sub-scanlines, exact horizontal coverage, source-over |
| `src/scan.rs` | the document: which elements and attributes, the two passes |
| `src/decoder.rs` | `Svg`, the `Decoder` implementation |
| `src/proofs.rs` | the Kani harnesses |

The image is drawn **at the size of the `Config` given to `start`**, which
need not be the intrinsic size `decode_config` reports: the `viewBox` is
mapped to the whole of it. A scaled use (a 10 px `background-size`, a 2x
display) is rasterized at its size. The pixels are straight RGBA8, as the
shape specifies; the renderer premultiplies with
`clazel_image_shape::premultiply`. The work buffer is the document (at most
8,192 bytes) plus 4 bytes per pixel of width.

MIME Sniffing has no SVG signature: the declared type (`image/svg+xml`)
selects this decoder, in `clazel-image` (not built yet).

Section 6.11a's plan also names the section numbers of SVG 2 as unconfirmed;
`src/lib.rs` pins them to the 06 October 2026 Candidate Recommendation
Snapshot and lists the ones used.

## Kani harnesses (`src/proofs.rs`)

Run in WSL Ubuntu with Kani 0.68.0 (`cargo kani -p clazel-svg --harness ...`):
**10 harnesses, 10 pass, 0 fail.** Under Kani the document buffer is 12
bytes and a path holds 4 edges (`src/limits.rs`; 8,192 and 256 in the
browser).

| Harness | Statement (every one: no panic, no overflow, no out-of-bounds index) | Bound | Time |
|---------|-----------|-------|------|
| `fraction_any` | the fraction rounding is at most 2^16 | every digit count to 9 and every value | 3 s |
| `number_any` | the number reader gives at most 2^20, ends after it starts and inside its input | any 5 bytes, any position | 13 s |
| `dimension_any` | `width`/`height` is 1 to 2^14 or an error | any 6 bytes | 8 s |
| `view_box_any` | a `viewBox` has positive size or is an error | any 8 bytes | 179 s |
| `fill_colour_any` | the colour reader | any 7 bytes | 6 s |
| `add_span_any` | a stretch of any `i64` ends adds exactly its overlap with each pixel (after the prefix sum) and nothing else | row of 2 pixels | 10 s |
| `scanline_any` | one scanline over edges of **any `i32` coordinates**, any accumulator contents | 3 edges, row of 2 pixels | 85 s |
| `resolve_row_any` | a row from any accumulator contents onto any pixels; an empty accumulator leaves the row | 2 pixels, any colour | 5 s |
| `composite_any` | source-over: alpha 0 keeps, 255 replaces, result alpha at least the coverage's and the destination's | every pixel, colour, alpha | 4 s |
| `fill_no_edges_any` | `fill` with no edges succeeds and changes nothing | 2 by 2, any contents | 11 s |

### What Kani does not cover (it was tried, and did not finish)

Harnesses for the following were written and run and **are not in the
crate**, because they did not complete (they are not failures of the code,
the checker gave up):

- **The tokenizer (`Reader`) and the path reader (`path::parse`) as wholes.**
  With the model checker's unwinding at 8 to 14 and inputs of 4 to 8 bytes
  CBMC reported unwinding assertions failing in `skip_space`, `name`, the
  digit loop of `number` and `skip_wsp` (loops whose bound is the input's
  length, which it did not relate to the symbolic slice), and ran out of
  memory at 6 GB. The pieces they call (`number`, `view_box`, `dimension`,
  `fill`) are proven; `Reader` and `path::parse` are covered by the unit
  tests, the 25,422 byte mutants and prefixes of the conformance test, and
  by the workspace lints (every index is `get`, every operation checked or
  saturating), not by a proof.
- **`Map` (the viewport transform) and `crossing` (where an edge meets a
  scanline).** 64-bit multiplication and division over symbolic values:
  timed out at 15 minutes even bounded to 2^10 and 2^12. Each is checked
  arithmetic throughout, so they cannot overflow or panic, but that is the
  lints', not a proof; the unit tests and the differential test cover their
  results.
- **`blend` (one colour channel of source-over lying between its inputs)**:
  timed out at 15 minutes (32-bit symbolic division); `composite_any` proves
  the alpha part only.
- **The whole `step` function** through item 6.3's `decoder_step_harness!`
  (document buffer 12 bytes, 2 by 2 image, chunks of 2): failed with the
  same unwinding and memory limits as the tokenizer. So `step`'s statement
  (keeps `inv` on every outcome, `consumed <= chunk.len()`, `NeedMore`
  consumes the whole chunk) is **not machine-checked**: it is exercised by
  the conformance test, which checks `inv` and these three after every step
  of every chunk size and every mutant, and is read from `collect` in
  `src/decoder.rs`.
- The bounds above: a row of 2 pixels, 3 edges, 12 bytes of document. The
  code is the same code with other constants.
- The tier stays 0 until CI's full verification has run these green
  (CLAUDE.md rule 7); and a tier 1 claim would need the tokenizer and path
  reader proven, which they are not.

## Tests

`tests/conformance_svg.rs` (18 tests) and 22 unit tests:

- HN's two files (`tests/fixtures/hn`, fetched 2026-11-16, SHA-256 in its
  `SOURCE.md`) through the `Decoder` interface at their intrinsic sizes
  (18 by 18; **32 by 32**) and at HN's `background-size` (10 by 10), with
  hand-checked pixels, mirror symmetry, centring at other aspect ratios.
- **tiny-skia 0.12.0** (the rasterizer of resvg; dev-dependency, class
  `test`) filling the same two paths, whose data a second float reader
  written for the test reads and whose `viewBox` transform is SVG 2 8.2
  transcribed again in `f32`: 8 sizes of `y18` and 9 of `triangle`. A pixel
  that is solid in both must agree **exactly** (0 mismatches); the
  anti-aliased ones differ by at most 43 of 255 (mean at most 0.93).
  Against the same picture drawn 16 times larger and averaged down, ours is
  within 6 and tiny-skia within 41: the difference is tiny-skia's
  quantisation, and the tolerance (48, mean 1.0) says so in the test. This is
  not resvg itself (which would add 24 packages, among them an XML parser and
  an image decoder), so the tokenizer is compared with nothing but the
  files and the corpus.
- Every chunk size 1 to 316 gives the same pixels and the same `consumed`;
  bytes after the root are not consumed; a prefix is never a frame.
- A corpus of refusals: 11 accepted documents and several dozen unsupported and
  malformed ones and 6 size errors, each with the right kind, and **the pixel
  buffer untouched** on every error, also when an earlier path was fine.
- 25,422 byte mutants (replace, delete, insert at every byte of both files)
  at three chunk sizes: never a panic, `inv` holds after every step, and
  the same outcome at every chunk size.

Under Miri the tiny-skia comparison is skipped and the others run with a
stride.

## Not done

`clazel-image` (dispatch on the declared `image/svg+xml`), `preserveAspectRatio`
other than the default, everything listed as refused above, comparison with
a browser's rendering, and the proofs listed under "What Kani does not
cover".
