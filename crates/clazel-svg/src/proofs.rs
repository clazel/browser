//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Under Kani the document buffer is 24 bytes and a path holds 4 edges
//! (`limits.rs`); every harness below is also bounded as its own comment
//! says, and the README lists the bounds and what they leave out.
//!
//! Every harness states "no panic, no overflow, no out-of-bounds index"
//! (Kani's built-in checks) for **all** values of its inputs within the
//! bound, and in addition:
//!
//! - [`fraction_any`], [`number_any`]: the number reader never gives more
//!   than 2^20 or reads outside its input, and always moves forward;
//! - [`reader_any`]: the tokenizer, over any 8 bytes, never moves past the
//!   end of the document;
//! - [`dimension_any`], [`view_box_any`], [`fill_colour_any`]: the
//!   attribute readers over any short value; a width or height is 1 to
//!   2^14, a `viewBox` has positive size;
//! - [`path_any`]: the path reader over any 6 bytes, whatever they are:
//!   at most the limit of edges, every device coordinate within 2^30;
//! - [`map_any`]: the viewport transform over **every** `viewBox` and size
//!   (not only small ones): device coordinates within 2^30, and the
//!   `viewBox` lands inside the viewport;
//! - [`crossing_any`], [`add_span_any`], [`scanline_any`],
//!   [`resolve_row_any`], [`fill_no_edges_any`], [`composite_any`]: the
//!   rasterizer, over edges of **any** `i32` coordinates, any accumulator
//!   contents and any pixels;
//! - [`step_any`]: item 6.3's template on the whole `step` function.

use crate::decoder::{Phase, Svg};
use crate::limits::{DOC_MAX, MAX_DEVICE, MAX_EDGES, MAX_NUMBER, ONE, UNIT};
use crate::map::{Map, ViewBox};
use crate::num::{fraction_fixed, number};
use crate::paint;
use crate::path::{self, Edge, Edges};
use crate::raster::{add_span, composite, crossing, fill, resolve_row, scanline};
use crate::scan::{dimension, view_box};
use crate::xml::Reader;
use clazel_image_shape::{Config, Error, Format, FrameCount, MAX_SIDE, SizeError};

/// The fraction rounding: for any digits and any count up to 9, at most
/// 2^16 (so the value of a number stays below `int + 1`).
#[kani::proof]
fn fraction_any() {
    let kept: usize = kani::any();
    kani::assume(kept <= 9);
    let frac: u64 = kani::any();
    kani::assume(frac < 10u64.pow(kept as u32));
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

/// The tokenizer over any 8 bytes: the prolog, then up to two items
/// (inside and outside the root's rules), never past the end.
#[kani::proof]
#[kani::unwind(11)]
fn reader_any() {
    let bytes: [u8; 8] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 8);
    let mut r = Reader::new(&bytes[..len]);
    let _ = r.prolog();
    assert!(r.pos() <= len);
    let _ = r.next_markup(kani::any());
    assert!(r.pos() <= len);
    let _ = r.next_markup(kani::any());
    assert!(r.pos() <= len);
}

/// `width` or `height` over any 6 bytes: 1 to `MAX_SIDE`, else an error.
#[kani::proof]
#[kani::unwind(8)]
fn dimension_any() {
    let bytes: [u8; 6] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 6);
    match dimension(&bytes[..len], SizeError::TooWide) {
        Ok(n) => assert!(n >= 1 && n <= MAX_SIDE),
        Err(Error::Size(SizeError::TooWide | SizeError::Empty)) => {}
        Err(_) => {}
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

/// Path data over any 6 bytes on a 2 by 2 image whose `viewBox` is 2 by 2:
/// on success at most `MAX_EDGES` edges, all within 2^30 device units.
#[kani::proof]
#[kani::unwind(9)]
fn path_any() {
    let bytes: [u8; 6] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 6);
    let vb = ViewBox {
        x: 0,
        y: 0,
        w: 2 * ONE,
        h: 2 * ONE,
    };
    let Ok(map) = Map::new(vb, 2, 2) else {
        return;
    };
    let mut edges = Edges::new();
    if path::parse(&bytes[..len], &map, &mut edges).is_ok() {
        let list = edges.as_slice();
        assert!(list.len() <= MAX_EDGES);
        for e in list {
            for c in [e.x0, e.y0, e.x1, e.y1] {
                assert!(i64::from(c).abs() <= MAX_DEVICE);
            }
        }
    }
}

/// The viewport transform over every `viewBox` (numbers up to 2^20 in
/// magnitude, positive size), every size to 2^14 and every point: never
/// panics or overflows, a result is within 2^30, and the `viewBox`'s corners
/// land inside the viewport (`meet`: the whole `viewBox` is visible).
#[kani::proof]
fn map_any() {
    let vb = ViewBox {
        x: kani::any(),
        y: kani::any(),
        w: kani::any(),
        h: kani::any(),
    };
    kani::assume(vb.x.abs() <= MAX_NUMBER && vb.y.abs() <= MAX_NUMBER);
    kani::assume(vb.w >= 1 && vb.w <= MAX_NUMBER && vb.h >= 1 && vb.h <= MAX_NUMBER);
    let width: u32 = kani::any();
    let height: u32 = kani::any();
    kani::assume(width >= 1 && width <= MAX_SIDE && height >= 1 && height <= MAX_SIDE);
    let Ok(map) = Map::new(vb, width, height) else {
        return;
    };
    let px: i64 = kani::any();
    let py: i64 = kani::any();
    kani::assume(px.abs() <= MAX_NUMBER && py.abs() <= MAX_NUMBER);
    if let Ok((dx, dy)) = map.apply(px, py) {
        assert!(i64::from(dx).abs() <= MAX_DEVICE && i64::from(dy).abs() <= MAX_DEVICE);
    }
    let ew = i64::from(width) * UNIT;
    let eh = i64::from(height) * UNIT;
    if let (Ok((x0, y0)), Ok((x1, y1))) =
        (map.apply(vb.x, vb.y), map.apply(vb.x + vb.w, vb.y + vb.h))
    {
        assert!(x0 >= 0 && y0 >= 0);
        assert!(i64::from(x1) <= ew && i64::from(y1) <= eh);
        assert!(x0 <= x1 && y0 <= y1);
    }
}

/// Where an edge crosses a scanline, for an edge of any `i32`
/// coordinates and any scanline: the direction is 1 or -1, the scanline is
/// in the edge's half-open vertical range, and `x` is between the edge's
/// ends.
#[kani::proof]
fn crossing_any() {
    let e = Edge {
        x0: kani::any(),
        y0: kani::any(),
        x1: kani::any(),
        y1: kani::any(),
    };
    let ys: i64 = kani::any();
    if let Some((x, dir)) = crossing(&e, ys) {
        assert!(dir == 1 || dir == -1);
        let (lo, hi) = (e.y0.min(e.y1), e.y0.max(e.y1));
        assert!(i64::from(lo) <= ys && ys < i64::from(hi));
        let (xl, xh) = (e.x0.min(e.x1), e.x0.max(e.x1));
        assert!(i64::from(xl) <= x && x <= i64::from(xh));
    }
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
#[kani::unwind(4)]
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
/// leaves the pixel, 255 replaces it, the result's alpha is at least the
/// coverage and at least the destination's, and every colour channel is
/// between the source's and the destination's.
#[kani::proof]
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
        if dst[3] > 0 {
            for k in 0..3 {
                let (lo, hi) = (rgb[k].min(dst[k]), rgb[k].max(dst[k]));
                assert!(out[k] >= lo && out[k] <= hi);
            }
        }
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

/// A state of any phase and any document length for a 1 or 2 pixel image,
/// for the template.
pub(crate) fn any_svg() -> Option<Svg> {
    let w: u32 = kani::any();
    let h: u32 = kani::any();
    kani::assume(w >= 1 && w <= 2 && h >= 1 && h <= 2);
    let config = Config::new(Format::Svg, w, h, FrameCount::Known(1)).ok()?;
    let phase = match kani::any::<u8>() % 3 {
        0 => Phase::Collect,
        1 => Phase::Done,
        _ => Phase::Spent,
    };
    let len: usize = kani::any();
    kani::assume(len <= DOC_MAX);
    Some(Svg { config, phase, len })
}

clazel_image_shape::decoder_step_harness! {
    #[kani::proof]
    #[kani::unwind(16)]
    #[kani::solver(kissat)]
    fn step_any for Svg {
        max_chunk: 2,
        max_pixels: 16,
        max_work: 40,
        any_state: any_svg,
    }
}
