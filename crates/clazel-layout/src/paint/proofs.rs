//! Kani harnesses for paint. Compiled only under `cargo kani`.
//!
//! As in `flow/proofs.rs` and `table/proofs.rs`: each harness checks one
//! step from any state satisfying its invariant (`state.rs`), or one
//! function on any input: no panic or overflow is reachable, and the
//! properties its contract states hold. The clip stack's steps are checked
//! from any state, so every document, of any size and depth, has them.
//!
//! Proved for every size (step harnesses): the clip stack
//! ([`clips_any`]: entering and leaving keep the invariant and pair up,
//! and the clip in force lies within each clip entered) and decoration
//! propagation ([`propagate_any`]). For any input: snapping a length
//! ([`snap_any`]: monotone, exact on whole pixels) and a rectangle
//! ([`snap_rect_any`], [`snap_tiles_any`]: neighbours share their edge),
//! premultiplying a colour ([`premultiply_any`]), the intersection of two
//! rectangles ([`intersect_any`]). On bounded values (within 2^22 px, where
//! nothing saturates): the border strips ([`border_rects_any`]) and a
//! decoration line ([`line_rect_any`]).
//!
//! Not covered, and why: the walk (`order.rs`), whose state is the
//! fragment tree, the task stack and the list; the unit and golden tests
//! run it.

use super::decor::{line_rect, propagate};
use super::geometry::{border_rects, intersect, premultiply, snap, snap_rect};
use super::state::{Clips, Decor, DeviceRect, Line};
use crate::flow::FontMetrics;
use crate::flow::fragment::{Rect, Sides};

/// 2^22 px in 1/64 px.
const BOUND: i32 = 1 << 28;

fn small(v: i32) -> bool {
    v > -BOUND && v < BOUND
}

fn any_scale() -> u32 {
    let s: u32 = kani::any();
    kani::assume((1..=16).contains(&s));
    s
}

/// Snapping is monotone, exact on whole CSS pixels, and never overflows.
#[kani::proof]
fn snap_any() {
    let (a, b): (i32, i32) = (kani::any(), kani::any());
    let s = any_scale();
    if a <= b {
        assert!(snap(a, s) <= snap(b, s));
    }
    let n: i32 = kani::any();
    kani::assume(n > -(1 << 20) && n < (1 << 20));
    assert!(i64::from(snap(n * 64, s)) == i64::from(n) * i64::from(s));
}

/// A snapped rectangle's size is its snapped far edges less its snapped
/// near ones.
#[kani::proof]
fn snap_rect_any() {
    let r: Rect = kani::any();
    kani::assume(r.width >= 0 && r.height >= 0);
    let s = any_scale();
    let d = snap_rect(r, s);
    assert!(d.x == snap(r.x, s) && d.y == snap(r.y, s));
    assert!(d.right() == i64::from(snap(r.right(), s)).max(i64::from(d.x)));
    assert!(d.bottom() == i64::from(snap(r.bottom(), s)).max(i64::from(d.y)));
}

/// Two rectangles that share an edge in CSS pixels share it in device
/// pixels: no gap and no overlap.
#[kani::proof]
fn snap_tiles_any() {
    let a: Rect = kani::any();
    kani::assume(small(a.x) && small(a.width) && a.width >= 0);
    let w: i32 = kani::any();
    kani::assume(w >= 0 && small(w));
    let b = Rect {
        x: a.x + a.width,
        width: w,
        ..a
    };
    let s = any_scale();
    assert!(snap_rect(a, s).right() == i64::from(snap_rect(b, s).x));
}

/// A premultiplied colour: no channel above the alpha; opaque keeps the
/// channels, transparent is 0.
#[kani::proof]
fn premultiply_any() {
    let c: [u8; 4] = kani::any();
    let p = premultiply(c);
    let a = p >> 24;
    assert!(a == u32::from(c[3]));
    assert!((p >> 16) & 0xff <= a && (p >> 8) & 0xff <= a && p & 0xff <= a);
    if c[3] == 255 {
        assert!(p == 0xff00_0000 | u32::from(c[0]) << 16 | u32::from(c[1]) << 8 | u32::from(c[2]));
    }
    if c[3] == 0 {
        assert!(p == 0);
    }
}

/// The intersection lies within both rectangles.
#[kani::proof]
fn intersect_any() {
    let (a, b): (DeviceRect, DeviceRect) = (kani::any(), kani::any());
    let c = intersect(a, b);
    if !c.is_empty() {
        assert!(i64::from(c.x) >= i64::from(a.x) && i64::from(c.x) >= i64::from(b.x));
        assert!(c.right() <= a.right() && c.right() <= b.right());
        assert!(i64::from(c.y) >= i64::from(a.y) && i64::from(c.y) >= i64::from(b.y));
        assert!(c.bottom() <= a.bottom() && c.bottom() <= b.bottom());
    }
}

/// The clip stack from any state: entering keeps the invariant, deepens by
/// one, pops only a clip in force and pushes one within the new rectangle
/// and the old clip; leaving to the clip that was in force undoes it.
#[kani::proof]
fn clips_any() {
    assert!(Clips::NONE.invariant());
    let c: Clips = kani::any();
    kani::assume(c.invariant() && c.depth < u32::MAX);
    let r: DeviceRect = kani::any();
    let (e, change) = c.enter(r);
    assert!(e.invariant());
    assert!(e.depth == c.depth + 1);
    assert!(change.pop == c.current.is_some());
    assert!(change.push.is_some());
    let Some(pushed) = change.push else {
        return;
    };
    assert!(e.current == Some(pushed));
    if !pushed.is_empty() {
        assert!(i64::from(pushed.x) >= i64::from(r.x) && pushed.right() <= r.right());
        if let Some(old) = c.current {
            assert!(i64::from(pushed.x) >= i64::from(old.x) && pushed.right() <= old.right());
        }
    }
    let (l, back) = e.leave(c.current);
    assert!(l == c);
    assert!(back.pop);
    assert!(back.push == c.current);
}

/// Decorations: an atomic inline starts afresh; otherwise the parent's
/// lines stay unless the box draws its own.
#[kani::proof]
fn propagate_any() {
    let parent: Decor = kani::any();
    let own: clazel_style::cascade::computed::DecorationLines = kani::any();
    let colour: [u8; 4] = kani::any();
    let cut: bool = kani::any();
    let d = propagate(parent, own, colour, cut);
    let base = if cut { Decor::default() } else { parent };
    assert!(
        d.underline
            == if own.underline {
                Some(colour)
            } else {
                base.underline
            }
    );
    assert!(
        d.overline
            == if own.overline {
                Some(colour)
            } else {
                base.overline
            }
    );
    assert!(
        d.line_through
            == if own.line_through {
                Some(colour)
            } else {
                base.line_through
            }
    );
}

/// The four border strips lie inside the border box and do not overlap.
#[kani::proof]
fn border_rects_any() {
    let b: Rect = kani::any();
    kani::assume(small(b.x) && small(b.y) && b.width >= 0 && b.height >= 0);
    kani::assume(b.width < BOUND && b.height < BOUND);
    let w: Sides = kani::any();
    let [top, right, bottom, left] = border_rects(b, w);
    for r in [top, right, bottom, left] {
        assert!(r.width >= 0 && r.height >= 0);
        assert!(r.x >= b.x && r.right() <= b.right());
        assert!(r.y >= b.y && r.bottom() <= b.bottom());
    }
    // Top above bottom, left and right between them and apart.
    assert!(top.bottom() <= bottom.y);
    assert!(left.y >= top.bottom() && left.bottom() <= bottom.y);
    assert!(right.y >= top.bottom() && right.bottom() <= bottom.y);
    assert!(left.right() <= right.x);
}

/// A decoration line spans its run and is as thick as the underline (at
/// least 1/64 px).
#[kani::proof]
fn line_rect_any() {
    let kind: Line = kani::any();
    let m = FontMetrics {
        ascent: kani::any(),
        descent: kani::any(),
        line_gap: kani::any(),
        x_height: kani::any(),
        average: kani::any(),
        maximum: kani::any(),
        underline_position: kani::any(),
        underline_thickness: kani::any(),
    };
    let (baseline, x, width): (i32, i32, i32) = (kani::any(), kani::any(), kani::any());
    let r = line_rect(kind, baseline, &m, x, width);
    assert!(r.x == x && r.width == width.max(0));
    assert!(r.height >= 1 && r.height == m.underline_thickness.max(1));
    if kind == Line::Underline && small(baseline) && small(m.underline_position) {
        assert!(r.y == baseline + m.underline_position);
    }
}
