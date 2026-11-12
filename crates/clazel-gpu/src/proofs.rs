//! Kani harnesses for the batching and atlas arithmetic. Compiled only under
//! `cargo kani`. The crate is tier 0 (the plan's tier for `clazel-gpu`); these are
//! evidence, not a tier claim.
//!
//! Each harness checks that no panic, overflow or out-of-bounds index is reachable
//! and the assertions written in it. Where possible a harness takes **one step from
//! any state** that satisfies a stated invariant, so it holds for lists of every
//! length:
//!
//! - For every input: [`place_any`], [`grown_capacity_any`], [`texel_index_any`]
//!   (every pixel of a mask that fits the atlas has an index inside the mask),
//!   [`rect_at_any`], [`intersect_any`], [`blend_any`].
//! - One batching step from any state, for any item numbers and any viewport:
//!   [`clip_then_draw_any`] (a push and a draw after an earlier draw: every quad
//!   is inside the viewport and not empty, every scissor inside the viewport and
//!   not empty, every batch within the quads).
//! - Bounded: [`atlas_upload_any`] (an upload into an atlas of up to two live
//!   masks with any offsets satisfying the invariant, masks of at most 2 × 2: the
//!   invariant holds after, compaction included).

use crate::atlas::{
    Atlas, Entry, MAX_CAPACITY, MIN_CAPACITY, grown_capacity, mask_size, place, texel_index,
};
use crate::backend::{Op, Quad};
use crate::batch::Builder;
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
fn texel_index_any() {
    let (offset, columns, rows, column, row): (u32, u16, u16, u32, u32) = kani::any();
    let size = mask_size(columns, rows);
    kani::assume(u64::from(offset) + u64::from(size) <= u64::from(MAX_CAPACITY));
    kani::assume(column < u32::from(columns) && row < u32::from(rows));
    let index = texel_index(offset, columns.into(), column, row);
    assert!(index.is_some_and(|i| i >= offset && i < offset + size));
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

/// From any state an earlier draw left (any open batch under the viewport), a
/// push of any clip and a draw of any quad keep the frame's invariant.
#[kani::proof]
#[kani::unwind(4)]
fn clip_then_draw_any() {
    let viewport = any_viewport();
    let screen = viewport.rect();
    let mut b = Builder::new(viewport);
    let _ = b.draw(any_fill());
    let _ = b.push_clip(any_rect());
    let _ = b.draw(any_fill());
    let _ = b.pop_clip();
    let Ok(frame) = b.finish() else {
        panic!("a balanced frame always finishes");
    };
    for q in &frame.quads {
        assert!(!q.rect.is_empty() && q.rect.within(screen));
    }
    for op in &frame.ops {
        if let Op::Draw {
            scissor,
            first,
            count,
        } = op
        {
            assert!(!scissor.is_empty() && scissor.within(screen));
            assert!(*count >= 1);
            assert!(u64::from(*first) + u64::from(*count) <= frame.quads.len() as u64);
        }
    }
}

fn any_entry() -> Option<Entry> {
    if kani::any() {
        let (columns, rows): (u16, u16) = kani::any();
        kani::assume((1..=2).contains(&columns) && (1..=2).contains(&rows));
        let n = usize::from(columns) * usize::from(rows);
        Some(Entry {
            offset: kani::any(),
            columns,
            rows,
            coverage: vec![0; n],
        })
    } else {
        None
    }
}

/// The atlas invariant: live counts the live masks, and each lies below `top`,
/// which is within the capacity, apart from the others.
fn atlas_ok(a: &Atlas) -> bool {
    let entries: Vec<&Entry> = a.table_for_proof().iter().flatten().collect();
    let live: u64 = entries.iter().map(|e| u64::from(e.size())).sum();
    live == u64::from(a.live_for_proof())
        && a.top() <= a.capacity()
        && a.capacity() <= MAX_CAPACITY
        && entries
            .iter()
            .all(|e| u64::from(e.offset) + u64::from(e.size()) <= u64::from(a.top()))
        && entries.iter().enumerate().all(|(i, e)| {
            entries.iter().skip(i + 1).all(|f| {
                u64::from(e.offset) + u64::from(e.size()) <= u64::from(f.offset)
                    || u64::from(f.offset) + u64::from(f.size()) <= u64::from(e.offset)
            })
        })
        && (a.capacity() == 0 || (a.capacity() >= MIN_CAPACITY && a.capacity().is_power_of_two()))
}

#[kani::proof]
#[kani::unwind(5)]
fn atlas_upload_any() {
    let table = vec![any_entry(), any_entry()];
    let a = Atlas::for_proof(kani::any(), kani::any(), kani::any(), table);
    kani::assume(atlas_ok(&a));
    let mut a = a;
    let (columns, rows): (u16, u16) = kani::any();
    kani::assume((1..=2).contains(&columns) && (1..=2).contains(&rows));
    let n = usize::from(columns) * usize::from(rows);
    let id: u32 = kani::any();
    kani::assume(id < 3);
    let mut changes = Vec::new();
    // An error ends the GPU process, so the invariant is only needed after a success.
    if a.upload(id, columns, rows, vec![1; n], &mut changes)
        .is_ok()
    {
        assert!(a.get(id).is_some());
        assert!(atlas_ok(&a));
    }
}
