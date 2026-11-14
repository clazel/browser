//! Differential test of `clazel-glyph-mask` against `ab_glyph_rasterizer`
//! (phase-5.md item 5.17): every glyph of every vendored font, at every
//! size from 8 to 72 px.
//!
//! The fonts are `clazel-font`'s vendored ones (`../clazel-font/tests/data/`,
//! through the tables `cargo xtask testdata` generates there), every face of
//! each; a CFF face, which `clazel-font` does not read (decision 5.0(c)),
//! has no glyphs here. Paths come from `clazel_font::outline::glyph_path`.
//! The quarter-pixel offset cycles with the glyph and size, so all sixteen
//! offsets are drawn.
//!
//! Two comparisons per mask, each printing one `clazel-conformance:` line
//! (`xtask/src/conformance.rs`) and its difference histogram:
//!
//! - **same lines** (the plan's check): `ab_glyph_rasterizer` accumulates
//!   our flattened lines (`flatten_path`), converted to `f32` pixels. Its
//!   accumulation is the same signed-area method in floating point, written
//!   by another author, so this tests the accumulation and the coverage
//!   scale. A unit is one mask; it passes when every pixel is within one
//!   coverage level of `ab_glyph_rasterizer`'s.
//! - **own curves**: `ab_glyph_rasterizer` draws the same contours with its
//!   own Bézier flattening (`draw_quad`, within about 0.14 px of the curve),
//!   so this also compares our flattening (within ¼ px). Two polylines each
//!   within those distances of the curve can be 0.39 px apart, which moves
//!   a pixel's coverage by at most 0.39 × √2 of a pixel, 141 levels; a unit
//!   passes when every pixel is within that bound. The histogram says how
//!   far apart they really are.
//!
//! Masks are compared at the same size and position, which both engines
//! take from our placement. The reference draws into a buffer one pixel
//! wider, every x moved right by one pixel, and its first column is
//! dropped: `ab_glyph_rasterizer` 0.1.10's `draw_line` skips a row's whole
//! piece when its left end rounds (in `f32`) to a hair below x = 0 in row
//! 0 (`if linestart_x0i < 0 { continue; }`), and since its running sum
//! runs on across rows, the lost cover then shifts every later pixel of the
//! mask. Before the margin, 2 of 325,845 masks (DejaVu Serif glyph 611 at
//! 10 px and glyph 694 at 70 px, each with a line ending on the mask's left
//! edge in row 0) differed by up to 124 levels; our masks of both match the
//! polygon's exact area (shoelace over the same lines) to 0.003 px², the
//! reference's were 1.0 px² and 2.2 px² short. The margin changes no
//! coverage the reference computes correctly.
//!
//! Under Miri, only masks of at most 64 × 64 are drawn, every 17,011th
//! (glyph, size) pair, stepped to directly (the plan: "Miri on 64×64 masks
//! only"), 19 masks, so the test takes about a minute (75 s); CI fails
//! a test that takes 300 s under Miri. Measured on Miri's clock: every
//! 34,019th pair (10 masks) took 38 s, every 21,701st (15) 35 s, every
//! 12,007th (28) 109 s, every 2,003rd 676 s.

mod dejavu {
    include!("../../clazel-font/tests/generated/fonts_dejavu.rs");
}
mod fontations {
    include!("../../clazel-font/tests/generated/fonts_fontations.rs");
}
mod source_code_pro {
    include!("../../clazel-font/tests/generated/fonts_source_code_pro.rs");
}
mod source_serif {
    include!("../../clazel-font/tests/generated/fonts_source_serif.rs");
}

use ab_glyph_rasterizer::{Rasterizer, point};
use clazel_font::Face;
use clazel_font::file::FontFile;
use clazel_font::outline::{Path, glyph_path};
use clazel_glyph_mask::accumulate::ONE;
use clazel_glyph_mask::segments::{Segment, for_each_segment};
use clazel_glyph_mask::{
    Error, Lines, MAX_SIDE, Mask, Offset, Point, Quarter, accumulate_lines, flatten_path, place,
};

/// The smallest and largest sizes, in pixels per em.
const SIZES: std::ops::RangeInclusive<i32> = 8..=72;

/// Under Miri: every this many (glyph, size) pairs, a prime so that the
/// sample walks through sizes and glyphs.
const MIRI_STRIDE: usize = 17_011;

/// Under Miri: the largest mask side drawn.
const MIRI_SIDE: u32 = 64;

/// The "own curves" bound, in coverage levels: ⌈(¼ + 0.144) × √2 × 255⌉.
const OWN_CURVES_BOUND: u8 = 142;

/// Every vendored font file: name, SHA-256 (as its `SOURCE.md` lists it,
/// printed with the report) and bytes.
fn fonts() -> Vec<(&'static str, &'static str, &'static [u8])> {
    let mut out = Vec::new();
    out.extend(dejavu::FONTS.iter().map(|c| (c.file, c.sha256, c.bytes)));
    out.extend(
        fontations::FONTS
            .iter()
            .map(|c| (c.file, c.sha256, c.bytes)),
    );
    out.extend(
        source_code_pro::FONTS
            .iter()
            .map(|c| (c.file, c.sha256, c.bytes)),
    );
    out.extend(
        source_serif::FONTS
            .iter()
            .map(|c| (c.file, c.sha256, c.bytes)),
    );
    out
}

fn quarter(n: usize) -> Quarter {
    match n % 4 {
        0 => Quarter::Zero,
        1 => Quarter::One,
        2 => Quarter::Two,
        _ => Quarter::Three,
    }
}

/// A unit counter with a histogram of the largest per-pixel difference of
/// each mask and of every pixel's difference.
#[derive(Default)]
struct Tally {
    pass: u64,
    fail: u64,
    /// Pixels by absolute difference, 0..=255.
    pixels: Vec<u64>,
    /// Masks by their largest difference.
    worst: Vec<u64>,
    first_failures: Vec<String>,
}

impl Tally {
    fn new() -> Self {
        Tally {
            pixels: vec![0; 256],
            worst: vec![0; 256],
            ..Tally::default()
        }
    }

    fn record(&mut self, ours: &Mask, theirs: &[u8], bound: u8, what: impl Fn() -> String) {
        let mut worst = 0u8;
        for (&a, &b) in ours.coverage.iter().zip(theirs) {
            let d = a.abs_diff(b);
            worst = worst.max(d);
            if let Some(n) = self.pixels.get_mut(usize::from(d)) {
                *n = n.saturating_add(1);
            }
        }
        if let Some(n) = self.worst.get_mut(usize::from(worst)) {
            *n = n.saturating_add(1);
        }
        if worst <= bound && ours.coverage.len() == theirs.len() {
            self.pass = self.pass.saturating_add(1);
        } else {
            self.fail = self.fail.saturating_add(1);
            if self.first_failures.len() < 10 {
                self.first_failures
                    .push(format!("{}: largest difference {worst}", what()));
            }
        }
    }

    fn report(&self, suite: &str) {
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail=0 fail={} total={}",
            self.pass,
            self.fail,
            self.pass.saturating_add(self.fail)
        );
        let row = |name: &str, h: &[u64]| {
            let cells: Vec<String> = h
                .iter()
                .enumerate()
                .filter(|&(_, &n)| n > 0)
                .map(|(d, n)| format!("{d}:{n}"))
                .collect();
            println!(
                "  {suite}, {name} by difference in levels: {}",
                cells.join(" ")
            );
        };
        row("pixels", &self.pixels);
        row("masks (largest pixel)", &self.worst);
        for f in &self.first_failures {
            println!("  FAIL {f}");
        }
    }
}

/// A reference rasterizer for a `w` × `h` mask, with the one-pixel left
/// margin the module explains.
fn reference(w: usize, h: usize) -> Rasterizer {
    Rasterizer::new(w.saturating_add(1), h)
}

/// `ab_glyph_rasterizer`'s coverage of a `w` × `h` mask drawn by
/// [`reference`], margin dropped, as bytes like ours:
/// `round(min(|a|, 1) × 255)`.
fn reference_bytes(r: &Rasterizer, w: usize, h: usize) -> Vec<u8> {
    let stride = w.saturating_add(1);
    let mut out = vec![0u8; w.saturating_mul(h)];
    r.for_each_pixel(|i, a| {
        let (row, col) = (
            i.checked_div(stride).unwrap_or(0),
            i.checked_rem(stride).unwrap_or(0),
        );
        if col == 0 {
            return;
        }
        let at = row.saturating_mul(w).saturating_add(col.saturating_sub(1));
        if let Some(o) = out.get_mut(at) {
            // In 0.0..=255.0 after the clamp, so the cast is exact.
            *o = (a.min(1.0) * 255.0).round() as u8;
        }
    });
    out
}

/// A point in mask units as the reference's pixels, one pixel right.
fn px(p: Point) -> ab_glyph_rasterizer::Point {
    point(p.x as f32 / ONE as f32 + 1.0, p.y as f32 / ONE as f32)
}

/// The reference drawing our flattened lines.
fn same_lines(lines: &Lines) -> Vec<u8> {
    let (w, h) = (lines.width as usize, lines.height as usize);
    let mut r = reference(w, h);
    for &(a, b) in &lines.lines {
        r.draw_line(px(a), px(b));
    }
    reference_bytes(&r, w, h)
}

/// The reference drawing the placed contours with its own Béziers.
fn own_curves(path: &Path, offset: Offset) -> Result<Vec<u8>, Error> {
    let placed = place::place(path, offset, MAX_SIDE)?;
    let (w, h) = (placed.width as usize, placed.height as usize);
    let mut r = reference(w, h);
    let mut start = 0usize;
    for &end in &placed.contour_ends {
        let contour = placed.points.get(start..end).unwrap_or(&[]);
        for_each_segment(contour, |s| {
            match s {
                Segment::Line(a, b) => r.draw_line(px(a), px(b)),
                Segment::Quad(a, c, b) => r.draw_quad(px(a), px(c), px(b)),
            }
            Ok(())
        })?;
        start = end;
    }
    Ok(reference_bytes(&r, w, h))
}

#[test]
fn vendored_glyphs_against_ab_glyph_rasterizer() {
    let mut same = Tally::new();
    let mut own = Tally::new();
    let mut errors = Vec::new();
    let mut pair = 0usize;
    let mut largest = (0u32, 0u32);
    let mut faces = Vec::new();
    for (file, sha256, bytes) in fonts() {
        let Ok(font) = FontFile::parse(bytes) else {
            errors.push(format!("{file}: not a font"));
            continue;
        };
        for index in 0..font.num_faces() {
            // A CFF face (5.0(c)) has no glyphs here.
            let Ok(face) = Face::parse(bytes, index) else {
                continue;
            };
            faces.push(format!(
                "{file} #{index} ({} glyphs, sha256 {sha256})",
                face.num_glyphs()
            ));
            // Every (glyph, size) pair natively; under Miri, every
            // MIRI_STRIDE-th pair counted across all faces, stepped to
            // directly (visiting every pair took most of Miri's time).
            let sizes = SIZES.count();
            let total = usize::from(face.num_glyphs()).saturating_mul(sizes);
            let (first, step) = if cfg!(miri) {
                let r = pair.checked_rem(MIRI_STRIDE).unwrap_or(0);
                (
                    MIRI_STRIDE
                        .saturating_sub(r)
                        .checked_rem(MIRI_STRIDE)
                        .unwrap_or(0),
                    MIRI_STRIDE,
                )
            } else {
                (0, 1)
            };
            pair = pair.saturating_add(total);
            for k in (first..total).step_by(step) {
                let glyph = u16::try_from(k.checked_div(sizes).unwrap_or(0)).unwrap_or(0);
                let size = SIZES
                    .start()
                    .saturating_add(i32::try_from(k.checked_rem(sizes).unwrap_or(0)).unwrap_or(0));
                let path = glyph_path(&face, glyph, size.saturating_mul(64));
                let n = usize::from(glyph).wrapping_add(size as usize);
                let offset = Offset {
                    x: quarter(n),
                    y: quarter(n / 4),
                };
                let lines = match flatten_path(&path, offset, MAX_SIDE) {
                    Ok(l) => l,
                    Err(e) => {
                        errors.push(format!("{file} #{index} glyph {glyph} at {size} px: {e:?}"));
                        continue;
                    }
                };
                if cfg!(miri) && (lines.width > MIRI_SIDE || lines.height > MIRI_SIDE) {
                    continue;
                }
                largest = (largest.0.max(lines.width), largest.1.max(lines.height));
                let ours = match accumulate_lines(&lines) {
                    Ok(m) => m,
                    Err(e) => {
                        errors.push(format!("{file} #{index} glyph {glyph} at {size} px: {e:?}"));
                        continue;
                    }
                };
                let what = || format!("{file} #{index} glyph {glyph} at {size} px, {offset:?}");
                same.record(&ours, &same_lines(&lines), 1, what);
                match own_curves(&path, offset) {
                    Ok(theirs) => own.record(&ours, &theirs, OWN_CURVES_BOUND, what),
                    Err(e) => errors.push(format!("{}: {e:?}", what())),
                }
            }
        }
    }
    same.report("ab_glyph_rasterizer, same lines");
    own.report("ab_glyph_rasterizer, own curves");
    println!("  largest mask: {} x {} px", largest.0, largest.1);
    for f in &faces {
        println!("  face: {f}");
    }
    for e in &errors {
        println!("  ERROR {e}");
    }
    assert!(errors.is_empty(), "{} glyphs had no mask", errors.len());
    assert_eq!(same.fail, 0, "same lines: masks beyond one level");
    assert_eq!(own.fail, 0, "own curves: masks beyond the bound");
    assert!(same.pass > 0);
}
