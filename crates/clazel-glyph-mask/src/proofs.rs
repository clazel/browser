//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Each harness runs one operation on **every** input within a stated
//! bound: Kani checks that no panic, arithmetic overflow or index out of
//! bounds is reachable, that every loop finishes within its unwinding bound,
//! and the assertions written below (chiefly: no [`Error::Overflow`], which
//! every checked step and every `get` returns instead of panicking). The
//! bounds are in each harness's name and comment, and in the crate's README.
//!
//! The plan asks for "every path up to a stated number of segments with any
//! 26.6 coordinates in `i32`, and every mask up to a stated size". CBMC's
//! formula grows fast with symbolic 64-bit multiplication and division, so
//! the harnesses are one step from any state, and none of them runs the
//! whole pipeline (see "Not covered" below):
//!
//! - Placement, for any `i32` coordinates, any offset and the real
//!   [`MAX_SIDE`]: [`place_screen_any`], [`place_box_any`] (the pixel box
//!   holds every point and fits the mask, else `TooLarge`) and
//!   [`place_local_any`] (a point in the box lands in the mask).
//! - The contour walk: [`segments_any_3`] (any contour of up to 3 points in
//!   a 1024-pixel mask, any flags).
//! - Flattening, for a Bézier anywhere in a 1024-pixel mask:
//!   [`pieces_any`] (a power of two up to 128 that meets the tolerance) and
//!   [`point_any_2`] and [`point_any_4`] (the interior points of a 2- and a
//!   4-piece cut stay in the control box).
//! - Accumulation: [`cell_any_1x1`] (one cell update in any state of a
//!   1 × 1 mask with cells within ±2⁵⁰, moving no cell by more than 2³¹),
//!   [`finish_row_any_6`] (any row of up to 6 pixels) and [`coverage_any`]
//!   (any running sum: 0..=255). A cell starts at 0 and a line moves it by
//!   at most 2³¹, so [`crate::MAX_LINES`] (2¹⁶) lines keep it within
//!   2⁴⁷ < 2⁵⁰, which the cell and finishing harnesses assume.
//!
//! Not covered by a harness (each has unit tests and is exercised by the
//! differential test, `tests/conformance_masks.rs`, on 325,845 masks up to
//! 159 × 97 px; every arithmetic step is checked, so a missed case returns
//! [`Error::Overflow`] rather than panicking or wrapping):
//!
//! - **A line's loops and its `x_at`/`y_at` division.** `x_at` for any line
//!   in a 1024-pixel mask (one 64-bit multiplication and one division) ran
//!   past 20 minutes; a whole line in a 1 × 1 mask passed 8 GB in 88 s. The
//!   argument instead: after the clamp, coordinates are in 0..=2²⁴, so the
//!   product is under 2⁵⁰ and the quotient lies between the line's ends;
//!   cell indices then come from coordinates inside the mask, and
//!   `cell` checks each index against the buffer.
//! - **A cell update in a mask larger than 1 × 1**: with a symbolic size up
//!   to 4 × 4 the harness passed 8 GB in 38 s. Its products are in `i32`
//!   with operands bounded by `ONE`, and its index is checked.
//! - **The placement loop over a path's points.** On 1 point it ran past 20
//!   minutes (and on 3 points it was a 2.6-million-step program); its
//!   arithmetic is the three placement harnesses above.
//! - **The whole pipeline** (`flatten_path` then `accumulate_lines`) on any
//!   path: it contains both of the above.
//! - **`B(i ÷ n)` for 8 to 128 pieces**: 4 pieces took 200 s; every
//!   `(n, i)` up to 8 pieces, each pair concrete, ran past 20 minutes, and
//!   so did `n` and `i` symbolic. The weights for 128 pieces are at most
//!   2¹⁵ and the coordinates 2²⁴, so each sum is under 2⁴¹, and the
//!   weights are non-negative and sum to `n²`, so the point lies in the
//!   control box.

use crate::accumulate::{Accumulator, ONE, Point, coverage, finish_row};
use crate::flatten::{self, MAX_PIECES, TOLERANCE};
use crate::place::{self, MaskBox};
use crate::segments::{Segment, for_each_segment};
use crate::{Error, MAX_SIDE, Offset, Quarter};

/// The bound on a cell's magnitude that the cell and finish harnesses
/// assume and keep (2⁵⁰).
const CELL_BOUND: i64 = 1 << 50;

/// The most a cell moves for one line (2³¹).
const LINE_STEP: i64 = 1 << 31;

/// The largest coordinate in a [`MAX_SIDE`] mask, in mask units (2²⁴).
const EXTENT: i64 = (MAX_SIDE as i64) * ONE;

fn any_quarter() -> Quarter {
    match kani::any::<u8>() % 4 {
        0 => Quarter::Zero,
        1 => Quarter::One,
        2 => Quarter::Two,
        _ => Quarter::Three,
    }
}

fn any_offset() -> Offset {
    Offset {
        x: any_quarter(),
        y: any_quarter(),
    }
}

fn inside(p: Point) -> bool {
    0 <= p.x && p.x <= EXTENT && 0 <= p.y && p.y <= EXTENT
}

fn any_mask_point() -> Point {
    let p = Point {
        x: kani::any(),
        y: kani::any(),
    };
    kani::assume(inside(p));
    p
}

/// Screen coordinates of any `i32` point at any offset: no overflow.
#[kani::proof]
fn place_screen_any() {
    assert!(place::screen(kani::any(), kani::any(), any_offset()).is_ok());
}

/// The box of any control box whose corners come from `i32` points at any
/// offset, in a mask of up to [`MAX_SIDE`]: either [`Error::TooLarge`] or
/// a box of at most that size holding the control box.
#[kani::proof]
fn place_box_any() {
    let (x0, y0) = (i64::from(kani::any::<i32>()), i64::from(kani::any::<i32>()));
    let (x1, y1) = (i64::from(kani::any::<i32>()), i64::from(kani::any::<i32>()));
    let (ox, oy) = (any_quarter().units(), any_quarter().units());
    let (x0, x1) = (x0 + ox, x1 + ox);
    let (y0, y1) = (oy - y1, oy - y0);
    kani::assume(x0 <= x1 && y0 <= y1);
    match place::mask_box(x0, y0, x1, y1, MAX_SIDE) {
        Err(e) => assert!(e == Error::TooLarge),
        Ok(MaskBox {
            left,
            top,
            width,
            height,
        }) => {
            let max = i64::from(MAX_SIDE);
            assert!(0 <= width && width <= max && 0 <= height && height <= max);
            assert!(left * 64 <= x0 && x1 <= (left + width) * 64);
            assert!(top * 64 <= y0 && y1 <= (top + height) * 64);
        }
    }
}

/// A screen coordinate inside a box of up to [`MAX_SIDE`] pixels at any
/// edge an `i32` coordinate can give lands in the mask: 0..=size × ONE.
#[kani::proof]
fn place_local_any() {
    let edge: i64 = kani::any();
    let size: i64 = kani::any();
    let v: i64 = kani::any();
    kani::assume(-(1 << 26) <= edge && edge <= 1 << 26);
    kani::assume(0 <= size && size <= i64::from(MAX_SIDE));
    kani::assume(edge * 64 <= v && v <= (edge + size) * 64);
    let l = place::to_local(v, edge);
    assert!(l.is_ok());
    let l = l.unwrap_or(-1);
    assert!(0 <= l && l <= size * ONE);
}

/// The walk of every contour of up to 3 points anywhere in a 1024-pixel
/// mask, any flags: never [`Error::Overflow`], and every segment's points
/// stay in the mask (implied midpoints lie between their points).
#[kani::proof]
#[kani::unwind(5)]
fn segments_any_3() {
    let n: usize = kani::any();
    kani::assume(n <= 3);
    let mut contour = Vec::new();
    for _ in 0..n {
        contour.push((any_mask_point(), kani::any::<bool>()));
    }
    let r = for_each_segment(&contour, |s| {
        match s {
            Segment::Line(a, b) => assert!(inside(a) && inside(b)),
            Segment::Quad(a, c, b) => assert!(inside(a) && inside(c) && inside(b)),
        }
        Ok(())
    });
    assert!(r.is_ok());
}

/// The piece count of every Bézier in a 1024-pixel mask: a power of two up
/// to [`MAX_PIECES`], and enough that `n² × 4 × TOLERANCE ≥ |d|₁`, the
/// flattening bound (so the cap never cuts a Bézier in the mask short).
#[kani::proof]
#[kani::unwind(9)]
fn pieces_any() {
    let (a, c, b) = (any_mask_point(), any_mask_point(), any_mask_point());
    let n = flatten::pieces(a, c, b);
    assert!(n.is_ok());
    let n = n.unwrap_or(0);
    assert!(n.is_power_of_two() && n <= MAX_PIECES);
    let d = (a.x - 2 * c.x + b.x).unsigned_abs() + (a.y - 2 * c.y + b.y).unsigned_abs();
    assert!(u64::from(n) * u64::from(n) * 4 * TOLERANCE >= d);
}

/// The midpoint `B(1 ÷ 2)` of every Bézier in a 1024-pixel mask (2 pieces,
/// the interior point): computed without overflow and inside the box of
/// the control points. Every `(n, i)` up to 8 pieces ran past 20 minutes.
#[kani::proof]
fn point_any_2() {
    let (a, c, b) = (any_mask_point(), any_mask_point(), any_mask_point());
    let q = flatten::point(a, c, b, 2, 1);
    assert!(q.is_ok());
    let q = q.unwrap_or(Point { x: -1, y: -1 });
    assert!(a.x.min(c.x).min(b.x) <= q.x && q.x <= a.x.max(c.x).max(b.x));
    assert!(a.y.min(c.y).min(b.y) <= q.y && q.y <= a.y.max(c.y).max(b.y));
}

/// The interior points `B(i ÷ 4)`, `i` = 1, 2, 3, of every Bézier in a
/// 1024-pixel mask: computed without overflow and inside the box of the
/// control points.
#[kani::proof]
fn point_any_4() {
    let (a, c, b) = (any_mask_point(), any_mask_point(), any_mask_point());
    let check = |i: u32| {
        let q = flatten::point(a, c, b, 4, i);
        assert!(q.is_ok());
        let q = q.unwrap_or(Point { x: -1, y: -1 });
        assert!(a.x.min(c.x).min(b.x) <= q.x && q.x <= a.x.max(c.x).max(b.x));
        assert!(a.y.min(c.y).min(b.y) <= q.y && q.y <= a.y.max(c.y).max(b.y));
    };
    check(1);
    check(2);
    check(3);
}

/// One cell update, as a line's piece makes it (either column of the row,
/// x offsets in 0..=ONE, height in −ONE..=ONE), in any state of a 1 × 1
/// mask whose three cells are within ±2⁵⁰: never [`Error::Overflow`] (no
/// overflow, no index outside the buffer), and no cell moves by more than
/// 2³¹. With a symbolic mask size up to 4 × 4 it passed 8 GB in 38 s.
#[kani::proof]
#[kani::unwind(4)]
fn cell_any_1x1() {
    let Ok(mut acc) = Accumulator::new(1, 1) else {
        panic!("a 1 x 1 accumulator always fits");
    };
    let before: [i64; 3] = kani::any();
    for &c in &before {
        kani::assume(-CELL_BOUND <= c && c <= CELL_BOUND);
    }
    assert!(acc.set_cells(&before));
    let col: i64 = kani::any();
    let (fxa, fxb, dy): (i64, i64, i64) = (kani::any(), kani::any(), kani::any());
    kani::assume(0 <= col && col <= 1);
    kani::assume(0 <= fxa && fxa <= ONE && 0 <= fxb && fxb <= ONE);
    kani::assume(-ONE <= dy && dy <= ONE);
    assert!(acc.cell(0, col, fxa, fxb, dy).is_ok());
    for (old, new) in before.iter().zip(acc.cells()) {
        assert!((new - old).abs() <= LINE_STEP);
    }
}

/// One row of the finishing pass: any row of up to 8 cells (a mask up to
/// 6 pixels wide, plus its two extra cells) within ±2⁵⁰, any width: every
/// running sum and coverage computed without overflow, one byte per pixel.
/// [`Accumulator::finish`] runs this on each row of its buffer
/// (`chunks_exact`, which cannot index outside it).
#[kani::proof]
#[kani::unwind(9)]
fn finish_row_any_6() {
    let cells: [i64; 8] = kani::any();
    let len: usize = kani::any();
    let width: usize = kani::any();
    kani::assume(len <= 8 && width <= 6 && width <= len);
    let row = cells.get(..len).unwrap_or(&[]);
    for &c in row {
        kani::assume(-CELL_BOUND <= c && c <= CELL_BOUND);
    }
    let mut out = Vec::new();
    assert!(finish_row(row, width, &mut out).is_ok());
    assert!(out.len() == width);
}

/// The coverage of any running sum is computed without overflow, and is
/// 255 exactly for a sum of at least a full cell in magnitude.
#[kani::proof]
fn coverage_any() {
    let run: i64 = kani::any();
    let c = coverage(run);
    assert!(c.is_ok());
    if run.unsigned_abs() >= crate::accumulate::FULL.unsigned_abs() {
        assert!(c == Ok(255));
    }
}
