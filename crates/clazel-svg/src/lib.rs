//! Static SVG for exactly the two files Hacker News uses (phase-6.md item
//! 6.11a): `y18.svg` (the logo) and `triangle.svg` (the vote arrow). A
//! decoder implementing [`clazel_image_shape::Decoder`] that parses the
//! document with a tokenizer of its own, reads the one path syntax those
//! files use, and rasterizes it to straight RGBA8 (the renderer
//! premultiplies with `clazel_image_shape::premultiply`).
//!
//! **Scope is exactly what those two files use, and no more.** Everything
//! else is refused as an [`Error`] (so the image is a broken image showing
//! its `alt`, decision 6.0(c)'s S1), never drawn in part. Phase 8 does SVG
//! in full.
//!
//! # The standards
//!
//! - *Scalable Vector Graphics (SVG) 2*, W3C Candidate Recommendation
//!   Snapshot, 06 October 2026,
//!   <https://www.w3.org/TR/2026/CR-SVG2-20261006/> (the plan's section
//!   numbers were marked unconfirmed; these are checked against that text,
//!   fetched 2026-11-16, SHA-256 of the whole-document page
//!   `14b38cf71a2e49bbb9e5671580e42ffe36ba1602c2737b7ad5b1c95825d0d225`).
//!   The sections used, all in that document:
//!   - 2.4.5 and 2.4.6 stand-alone files and error processing (see
//!     choice 6);
//!   - 3.11 the `overflow` property (the root `svg`'s is `visible`, and
//!     the image is clipped by the box it is drawn in: choice 5);
//!   - 5.1.2 namespace, 5.1.4 the `svg` element;
//!   - 8.2 computing the equivalent transform of an SVG viewport (`map.rs`,
//!     with the steps quoted), 8.3 the initial viewport, 8.6 `viewBox`, 8.7
//!     `preserveAspectRatio` (default `xMidYMid meet`), 8.12 intrinsic
//!     sizing properties of SVG content;
//!   - 9.2 the `path` element, 9.3.2 `d`, 9.3.3 moveto, 9.3.4 closepath,
//!     9.3.5 lineto (`L`, `H`, `V`), 9.3.9 the grammar for path data, 9.5.4
//!     error handling in path data (`path.rs`, `num.rs`);
//!   - 13.4.1 `fill` (initial value black), 13.4.2 `fill-rule` (initial
//!     value `nonzero`, `raster.rs`).
//! - *Extensible Markup Language (XML) 1.0 (Fifth Edition)*, W3C
//!   Recommendation 26 November 2008: sections 2.3, 2.5, 2.8, 3.1, 3.3.3
//!   (`xml.rs` lists which are read and which refused).
//! - *CSS Color Module Level 4*, section 6.1 (RGB hexadecimal notations):
//!   `#rgb` and `#rrggbb` (`paint.rs`).
//!
//! # What is read
//!
//! Elements `svg` and `path`. Attributes `xmlns` (the SVG namespace),
//! `width`, `height`, `viewBox` on `svg`; `d`, `fill` on `path`. Path
//! commands `M`/`m`, `L`/`l`, `H`/`h`, `V`/`v`, `Z`/`z`, including the
//! implicit `lineto` after a `moveto`, numbers as signed decimal fractions.
//! `fill` as `#rgb` or `#rrggbb`. The `nonzero` fill rule, the default
//! `preserveAspectRatio`. The XML declaration and comments are skipped.
//! **Refused:** every other element, attribute, command or colour syntax,
//! `style`, entities, `DOCTYPE`, `CDATA`, processing instructions,
//! namespace prefixes, text; among what Wikipedia's SVGs need and HN's do
//! not: gradients, `g`, `circle`, `rect`, `clipPath`, `defs`, `transform`,
//! `style`, strokes, curves, metadata.
//!
//! # Modelling choices
//!
//! 1. **The size drawn is the config's.** `decode_config` reports the
//!    intrinsic size (`width` and `height`, section 8.12); `start` takes any
//!    [`Config`](clazel_image_shape::Config) of format `Svg` and draws at
//!    that size, so a scaled use (a 10 px `background-size`, a 2x display)
//!    is rasterized at its size, not scaled afterwards.
//! 2. **`preserveAspectRatio` is always `xMidYMid meet`** (section 8.7's
//!    initial value; the attribute itself is refused). Drawn at another
//!    aspect ratio than the `viewBox`'s, the content is centred with
//!    transparent bars.
//! 3. **No `viewBox`** means `0 0 width height` (the user space is the
//!    intrinsic size), as browsers draw an `img` of such a file.
//! 4. **`width` and `height` are required and are whole numbers of pixels**
//!    (digits only: no unit, no fraction, no percentage). Section 8.12
//!    derives the size from the `viewBox` when they are absent, but only an
//!    aspect ratio then, and a [`Config`](clazel_image_shape::Config) needs
//!    a size. Both files state them.
//! 5. **Clipping is to the viewport** (the box the image is drawn in),
//!    which section 3.11 gives for the root element: its `overflow` is
//!    `visible` and the host replaced box clips. For both files, and for
//!    any size of the same aspect ratio, that is the `viewBox` too; with
//!    `meet` at another aspect ratio, content outside the `viewBox` but
//!    inside the box is drawn (as browsers draw it).
//! 6. **An error anywhere refuses the whole image.** Section 9.5.4 says a
//!    `path` is rendered "up to (but not including) the path command
//!    containing the first error"; this decoder refuses the image
//!    instead (the plan: "never a partial draw"), through two passes
//!    (`scan.rs`). A `viewBox` with a non-positive width or height is also
//!    refused (section 8.6: a negative one is treated as absent, a zero one
//!    disables rendering).
//! 7. **Numbers** are read to 9 fraction digits, rounded to units of
//!    2^-16, magnitude at most 2^20; the exponent and a trailing point
//!    (`23.`, which section 9.3.9 disallows but lets an agent accept) are
//!    refused. User coordinates map to device coordinates in 1/256
//!    pixel (`map.rs`), which must stay within 2^30 (2^22 pixels).
//! 8. **Limits**: the document at most 8,192 bytes (`limits.rs`), a path at
//!    most 256 edges (closing edges counted), a tag at most 4 attributes (the four that `svg` can have).
//!    HN's files are 315 and 131 bytes with 13 and 3 edges.
//! 9. **The document ends at the root's end tag**: `step` says `FrameDone`
//!    there and the bytes after it are not read, not even checked to be
//!    white space and comments (XML's `Misc*`). An unclosed root is
//!    [`Error::Truncated`] only through the caller, as for every decoder.
//! 10. **Comments** run to the first `-->`; `--` inside one (not
//!     well-formed, XML 1.0 section 2.5) is not checked. The XML
//!     declaration's version and encoding are not read; the bytes in
//!     comments are not checked to be valid UTF-8.
//! 11. **Anti-aliasing**: 16 sub-scanlines per pixel row with exact
//!     horizontal coverage (`raster.rs`), alpha rounded to 8 bits, source-over
//!     compositing in straight RGBA. Section 3.7.1 does not fix an
//!     algorithm; the tests compare with tiny-skia, the rasterizer of
//!     resvg, and state a tolerance.
//!
//! # Verification
//!
//! Tier 1 target (`Cargo.toml`): Kani harnesses in `proofs.rs`, listed with
//! their bounds in the README. Every index is `get`, every operation
//! checked or saturating, as the workspace lints require. The tier stays 0
//! until CI's full verification has run them (CLAUDE.md rule 7).

mod decoder;
mod limits;
mod map;
mod num;
mod paint;
mod path;
#[cfg(kani)]
mod proofs;
mod raster;
mod scan;
mod xml;

pub use clazel_image_shape::Error;
pub use decoder::Svg;
