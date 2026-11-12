//! Kani harnesses for the batching and atlas arithmetic. Compiled only under
//! `cargo kani`. The crate is tier 0 (the plan's tier for `clazel-gpu`); these are
//! evidence, not a tier claim.
//!
//! Each harness checks that no panic, overflow or out-of-bounds index is reachable
//! and the assertions written in it. Where possible a harness takes **one step from
//! any state** that satisfies a stated invariant, so it holds for lists of every
//! length:
//!
//! - For every input: [`place_any`], [`grown_capacity_any`] (from any capacity
//!   the atlas can hold), [`rect_at_any`], [`intersect_any`], [`blend_any`].
//!
//! Not covered: `atlas::texel_index` (every pixel of a mask that fits the atlas
//! has an index inside the mask). Its harness, for any `u16` sides and later with
//! sides up to 2048, reached the 20-minute cap twice at 0.17 GB (the 32-bit
//! multiplications) and was removed. Every step of it is checked, so a missed case
//! returns `None` and an error rather than panicking or wrapping; the unit tests
//! and every scene through the fake backend exercise it.
//! - The draw step's cut, for every input: [`visible_any`] (a recorded quad is
//!   inside the viewport and not empty, under a scissor that is not empty).
//! - Bounded to one draw: [`clip_then_draw_any`] (any viewport, any clip, any
//!   quad, from a fresh frame: one quad and one batch over it, or nothing). Batching
//!   across many draws (`Builder::close`'s indices) is covered by the unit tests and
//!   the scenes, not by a harness.
//!
//! Also not covered: an atlas upload from any state (`Atlas::upload`, compaction
//! included). Its harness, over two live masks of at most 2 × 2 with any offsets
//! meeting the invariant, passed the 8 GB cap in 83 s and was removed. The unit
//! tests in `atlas.rs` and the scene "atlas", which compacts in the middle of a
//! list, cover it; every step is checked.

use crate::atlas::{MAX_CAPACITY, MIN_CAPACITY, grown_capacity, place};
use crate::backend::{Op, Quad};
use crate::batch::{Builder, visible};
use crate::geom::{MAX_VIEWPORT_SIDE, Rect, Viewport};
use crate::soft::blend;

#[kani::proof]
fn place_any() {
    let (capacity, top, size): (u32, u32, u32) = kani::any();
    if let Some(offset) = place(capacity, top, size) {
        assert!(offset == top);
        assert!(u64::from(offset) + u64::from(size) <= u64::from(capacity));
    } else {
        assert!(u64::from(top) + u64::from(size) > u64::from(capacity));
    }
}

#[kani::proof]
#[kani::unwind(9)]
fn grown_capacity_any() {
    let (current, total): (u32, u32) = kani::any();
    // The atlas's invariant: no store yet, or one this function made.
    kani::assume(
        current == 0
            || (current.is_power_of_two() && (MIN_CAPACITY..=MAX_CAPACITY).contains(&current)),
    );
    match grown_capacity(current, total) {
        Some(c) => {
            assert!(c >= total);
            assert!((MIN_CAPACITY..=MAX_CAPACITY).contains(&c));
            assert!(c.is_power_of_two());
        }
        None => assert!(total > MAX_CAPACITY),
    }
}

#[kani::proof]
fn rect_at_any() {
    let (x, y, w, h): (i32, i32, u32, u32) = kani::any();
    if let Some(r) = Rect::at(x, y, w, h) {
        assert!(i64::from(r.x1) - i64::from(r.x0) == i64::from(w));
        assert!(i64::from(r.y1) - i64::from(r.y0) == i64::from(h));
    }
    // Every rectangle of a list that passed the validator is representable.
    let bound = 1i32 << 23;
    if (-bound..=bound).contains(&x)
        && (-bound..=bound).contains(&y)
        && w <= 1 << 23
        && h <= 1 << 23
    {
        assert!(Rect::at(x, y, w, h).is_some());
    }
}

fn any_rect() -> Rect {
    Rect {
        x0: kani::any(),
        y0: kani::any(),
        x1: kani::any(),
        y1: kani::any(),
    }
}

#[kani::proof]
fn intersect_any() {
    let (a, b) = (any_rect(), any_rect());
    let i = a.intersect(b);
    assert!(i.within(a) && i.within(b));
    let (px, py): (i32, i32) = kani::any();
    assert!(i.contains(px, py) == (a.contains(px, py) && b.contains(px, py)));
}

#[kani::proof]
fn blend_any() {
    let (c, a, k, d): (u8, u8, u8, u8) = kani::any();
    let out = blend(c, a, k, d);
    if k == 0 {
        assert!(out == d);
    }
    if k == 255 && a == 255 {
        assert!(out == c);
    }
    if c <= a {
        // A well-formed premultiplied colour never brightens past its own alpha's
        // share plus what was kept: out <= c + d, with no clamp needed.
        assert!(u32::from(out) <= u32::from(c) + u32::from(d));
    }
}

fn any_viewport() -> Viewport {
    let (w, h): (u32, u32) = kani::any();
    kani::assume((1..=MAX_VIEWPORT_SIDE).contains(&w) && (1..=MAX_VIEWPORT_SIDE).contains(&h));
    Viewport {
        width: w,
        height: h,
    }
}

fn any_fill() -> Quad {
    Quad {
        rect: any_rect(),
        origin_x: kani::any(),
        origin_y: kani::any(),
        offset: kani::any(),
        columns: kani::any(),
        colour: kani::any(),
    }
}

/// What a draw keeps: the quad it records is inside the viewport and not empty,
/// and its scissor is not empty, for any rectangles at all.
#[kani::proof]
fn visible_any() {
    let (rect, screen, scissor) = (any_rect(), any_rect(), any_rect());
    if let Some(cut) = visible(rect, screen, scissor) {
        assert!(!cut.is_empty() && cut.within(screen) && cut.within(rect));
        assert!(!scissor.is_empty() && !cut.intersect(scissor).is_empty());
    }
}

/// One draw under one clip from a fresh frame of any viewport: the frame's
/// batch covers exactly the recorded quad and its scissor is inside the viewport.
/// (A first form, with a draw before the clip, passed the 8 GB cap in 21 s.)
#[kani::proof]
#[kani::unwind(3)]
fn clip_then_draw_any() {
    let viewport = any_viewport();
    let screen = viewport.rect();
    let mut b = Builder::new(viewport);
    let _ = b.push_clip(any_rect());
    let _ = b.draw(any_fill());
    let _ = b.pop_clip();
    let Ok(frame) = b.finish() else {
        panic!("a balanced frame always finishes");
    };
    match (frame.quads.as_slice(), frame.ops.as_slice()) {
        ([], []) => {}
        (
            [q],
            [
                Op::Draw {
                    scissor,
                    first: 0,
                    count: 1,
                },
            ],
        ) => {
            assert!(!q.rect.is_empty() && q.rect.within(screen));
            assert!(!scissor.is_empty() && scissor.within(screen));
        }
        _ => panic!("one draw makes one quad and one batch, or nothing"),
    }
}
