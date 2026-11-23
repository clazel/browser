//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Under Kani the document buffer is 12 bytes and a path holds 4 edges
//! (`limits.rs`); each harness is also bounded as its comment says, and the
//! README lists the bounds and **what no harness covers** (the tokenizer
//! and the path reader as wholes, the viewport transform and the crossing
//! computation: harnesses for them did not finish).
//!
//! Every harness states "no panic, no overflow, no out-of-bounds index"
//! (Kani's built-in checks) for **all** values of its inputs within the
//! bound, and in addition:
//!
//! - [`fraction_any`], [`number_any`]: the number reader never gives more
//!   than 2^20 and always moves forward inside its input;
//! - [`dimension_any`], [`view_box_any`], [`fill_colour_any`]: the
//!   attribute readers over any short value; a width or height is 1 to
//!   2^14, a `viewBox` has positive size;
//! - [`add_span_any`], [`scanline_any`], [`resolve_row_any`],
//!   [`fill_no_edges_any`], [`composite_any`]: the rasterizer, over edges of
//!   **any** `i32` coordinates, any accumulator contents and any pixels;
//!   a stretch adds exactly its overlap with each pixel.

use crate::limits::{MAX_NUMBER, ONE, UNIT};
use crate::num::{fraction_fixed, number};
use crate::paint;
use crate::path::Edge;
use crate::raster::{add_span, composite, fill, resolve_row, scanline};
use crate::scan::{dimension, view_box};
use clazel_image_shape::{MAX_SIDE, SizeError};

/// The fraction rounding: for any digits and any count up to 9, at most
/// 2^16 (so the value of a number stays below `int + 1`).
#[kani::proof]
fn fraction_any() {
    let kept: usize = kani::any();
    kani::assume(kept <= 9);
    let frac: u64 = kani::any();
    let scale = [
        1u64,
        10,
        100,
        1_000,
        10_000,
        100_000,
        1_000_000,
        10_000_000,
        100_000_000,
        1_000_000_000,
    ][kept];
    kani::assume(frac < scale);
    let v = fraction_fixed(frac, kept);
    assert!(v <= ONE as u64);
    if frac == 0 {
        assert!(v == 0);
    }
}

/// The number reader over any 5 bytes from any position (also past the
/// end): the value is at most 2^20 in magnitude, the end is after the
/// start and inside the input.
#[kani::proof]
#[kani::unwind(8)]
fn number_any() {
    let bytes: [u8; 5] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 5);
    let pos: usize = kani::any();
    kani::assume(pos <= 6);
    let s = &bytes[..len];
    if let Ok(Some((v, end))) = number(s, pos) {
        assert!(end > pos && end <= len);
        assert!(v >= -MAX_NUMBER && v <= MAX_NUMBER);
    }
}

/// `width` or `height` over any 6 bytes: 1 to `MAX_SIDE`, else an error.
#[kani::proof]
#[kani::unwind(8)]
fn dimension_any() {
    let bytes: [u8; 6] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 6);
    if let Ok(n) = dimension(&bytes[..len], SizeError::TooWide) {
        assert!(n >= 1 && n <= MAX_SIDE);
    }
}

/// A `viewBox` over any 8 bytes: positive width and height or an error.
#[kani::proof]
#[kani::unwind(10)]
fn view_box_any() {
    let bytes: [u8; 8] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 8);
    if let Ok(vb) = view_box(&bytes[..len]) {
        assert!(vb.w > 0 && vb.h > 0);
    }
}

/// `fill` over any 7 bytes.
#[kani::proof]
#[kani::unwind(9)]
fn fill_colour_any() {
    let bytes: [u8; 7] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 7);
    let _ = paint::fill(&bytes[..len]);
}

/// A stretch `[a, b)` of any `i64` ends added to an empty accumulator for
/// a row of 2 pixels: the coverage of each pixel after the prefix sum is
/// exactly the overlap of the stretch with that pixel (in 1/256), and
/// nothing outside the accumulator is touched.
#[kani::proof]
#[kani::unwind(6)]
fn add_span_any() {
    let mut acc = [0u8; 16];
    let (a, b): (i64, i64) = (kani::any(), kani::any());
    assert!(add_span(&mut acc, 2 * UNIT, a, b).is_some());
    let entry = |i: usize| -> i64 {
        i64::from(i32::from_le_bytes([
            acc[4 * i],
            acc[4 * i + 1],
            acc[4 * i + 2],
            acc[4 * i + 3],
        ]))
    };
    let (ca, cb) = (a.clamp(0, 2 * UNIT), b.clamp(0, 2 * UNIT));
    let overlap = |lo: i64, hi: i64| -> i64 { (cb.min(hi) - ca.max(lo)).max(0) };
    let p0 = entry(0);
    let p1 = p0 + entry(1);
    let p2 = p1 + entry(2);
    assert!(p0 == overlap(0, UNIT));
    assert!(p1 == overlap(UNIT, 2 * UNIT));
    assert!(p2 == 0);
}

/// One scanline over up to 3 edges of **any** `i32` coordinates and any
/// scanline, with any accumulator contents (a row of 2 pixels): no panic.
#[kani::proof]
#[kani::unwind(5)]
fn scanline_any() {
    let edges: [Edge; 3] = [
        Edge {
            x0: kani::any(),
            y0: kani::any(),
            x1: kani::any(),
            y1: kani::any(),
        },
        Edge {
            x0: kani::any(),
            y0: kani::any(),
            x1: kani::any(),
            y1: kani::any(),
        },
        Edge {
            x0: kani::any(),
            y0: kani::any(),
            x1: kani::any(),
            y1: kani::any(),
        },
    ];
    let n: usize = kani::any();
    kani::assume(n <= 3);
    let mut acc: [u8; 16] = kani::any();
    let ys: i64 = kani::any();
    let _ = scanline(&edges[..n], ys, 2 * UNIT, &mut acc);
}

/// A row resolved from any accumulator contents onto any pixels (2 pixels,
/// any colour): no panic or overflow, and a fully transparent row stays
/// transparent when the accumulator is all zero.
#[kani::proof]
#[kani::unwind(17)]
fn resolve_row_any() {
    let acc: [u8; 16] = kani::any();
    let mut row: [u8; 8] = kani::any();
    let rgb: [u8; 3] = kani::any();
    let _ = resolve_row(&acc, &mut row, rgb);
    let zero = [0u8; 16];
    let mut empty = [0u8; 8];
    assert!(resolve_row(&zero, &mut empty, rgb).is_some());
    assert!(empty == [0u8; 8]);
}

/// Source-over for every destination pixel, colour and coverage: alpha 0
/// leaves the pixel, 255 replaces it, and the result's alpha is at least the
/// coverage and at least the destination's. (The colour channels are
/// `blend_any`'s.)
#[kani::proof]
#[kani::solver(kissat)]
fn composite_any() {
    let dst: [u8; 4] = kani::any();
    let rgb: [u8; 3] = kani::any();
    let a: u8 = kani::any();
    let out = composite(dst, rgb, a);
    if a == 0 {
        assert!(out == dst);
    }
    if a == 255 {
        assert!(out == [rgb[0], rgb[1], rgb[2], 255]);
    }
    if a > 0 {
        assert!(out[3] >= a && out[3] >= dst[3]);
    }
}

/// `fill` with no edges on a 2 by 2 image: succeeds and leaves any pixels
/// as they were.
#[kani::proof]
#[kani::unwind(19)]
fn fill_no_edges_any() {
    let mut pixels: [u8; 16] = kani::any();
    let before = pixels;
    let mut acc: [u8; 16] = kani::any();
    let rgb: [u8; 3] = kani::any();
    assert!(fill(&[], 2, 2, rgb, &mut pixels, &mut acc).is_ok());
    assert!(pixels == before);
}
