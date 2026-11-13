//! One frame: the items of a page's display list (item 5.16) that meet the
//! viewport at the scroll offset, offset by it, with the glyph masks (item
//! 5.17) the GPU process does not hold yet, as item 5.17a's items, encoded
//! and framed for the GPU process's socket (phase-5.md item 5.20).
//!
//! Modelling choices: `mod.rs`'s "Glyph masks", "Frames are bounded" and
//! "The socket's framing". Contracts: `state.rs`.

use std::collections::HashMap;

use clazel_displaylist::exec::{ExecItem, encode_list};
use clazel_displaylist::spec::{MAX_ITEMS, MAX_MASK_BYTES, MAX_MASKS};
use clazel_font::outline::glyph_path;
use clazel_glyph_mask::{Offset, Quarter, glyph_mask};
use clazel_layout::paint::{DeviceRect, DisplayList, Item};

use super::fonts::Fonts;
use super::state::Masks;

/// The most fill, clip and glyph items in one frame (`mod.rs`).
pub const MAX_DRAWS: usize = MAX_ITEMS / 2;

impl Masks {
    /// A new mask of `bytes` coverage bytes (`state.rs`'s contract).
    pub fn allocate(&self, bytes: u64) -> Option<(Masks, u32)> {
        let max_masks = u32::try_from(MAX_MASKS).unwrap_or(u32::MAX);
        let max_bytes = u64::try_from(MAX_MASK_BYTES).unwrap_or(u64::MAX);
        if self.live >= max_masks || self.bytes.saturating_add(bytes) > max_bytes {
            return None;
        }
        let mut next = self.clone();
        let id = match next.free.pop() {
            Some(id) => id,
            None if next.next < max_masks => {
                let id = next.next;
                next.next = next.next.saturating_add(1);
                id
            }
            None => return None,
        };
        next.live = next.live.saturating_add(1);
        next.bytes = next.bytes.saturating_add(bytes);
        Some((next, id))
    }

    /// Mask `id` of `bytes` coverage bytes is freed (`state.rs`'s contract).
    pub fn release(&self, id: u32, bytes: u64) -> Masks {
        let mut next = self.clone();
        next.live = next.live.saturating_sub(1);
        next.bytes = next.bytes.saturating_sub(bytes);
        next.free.push(id);
        next
    }
}

/// What identifies a glyph's mask: its face, glyph, size (1/64 device px
/// per em) and quarter-pixel offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Key {
    face: u32,
    glyph: u16,
    size: i32,
    x: u8,
    y: u8,
}

/// A live mask: its id, where it sits from the glyph's origin, its size.
#[derive(Debug, Clone, Copy)]
struct Live {
    id: u32,
    left: i32,
    top: i32,
    bytes: u64,
}

/// The masks the GPU process holds for this renderer, across frames.
#[derive(Default)]
pub struct MaskCache {
    masks: Masks,
    live: HashMap<Key, Live>,
    /// Glyphs with no mask (an empty outline, or one too large).
    empty: HashMap<Key, ()>,
}

/// The quarter of a pixel `v` (1/64 px) falls in, and its whole pixel,
/// rounded down.
fn split(v: i32) -> (i32, Quarter) {
    let whole = v.div_euclid(64);
    let q = match v.rem_euclid(64).div_euclid(16) {
        0 => Quarter::Zero,
        1 => Quarter::One,
        2 => Quarter::Two,
        _ => Quarter::Three,
    };
    (whole, q)
}

fn quarter_number(q: Quarter) -> u8 {
    match q {
        Quarter::Zero => 0,
        Quarter::One => 1,
        Quarter::Two => 2,
        Quarter::Three => 3,
    }
}

/// `r` moved up by `scroll` and cut to a viewport `w` by `h`, if any of it
/// is inside.
fn in_view(r: DeviceRect, scroll: i64, w: u32, h: u32) -> Option<(i32, i32, u32, u32)> {
    let x0 = i64::from(r.x).max(0);
    let y0 = i64::from(r.y).saturating_sub(scroll).max(0);
    let x1 = r.right().min(i64::from(w));
    let y1 = r.bottom().saturating_sub(scroll).min(i64::from(h));
    if x1 <= x0 || y1 <= y0 {
        return None;
    }
    Some((
        i32::try_from(x0).ok()?,
        i32::try_from(y0).ok()?,
        u32::try_from(x1.saturating_sub(x0)).ok()?,
        u32::try_from(y1.saturating_sub(y0)).ok()?,
    ))
}

/// The items of one frame of `list` in a viewport `w` by `h` whose top is
/// `scroll` device pixels down the page, drawing glyphs from `fonts`, with
/// the masks the GPU process holds in `cache` (updated).
pub fn frame(
    list: &DisplayList,
    w: u32,
    h: u32,
    scroll: i64,
    fonts: &Fonts,
    cache: &mut MaskCache,
) -> Vec<ExecItem> {
    // The glyphs this frame draws, and its fills and clips, in order.
    enum Draw {
        Item(ExecItem),
        Glyph {
            key: Key,
            x: i32,
            y: i32,
            colour: u32,
        },
    }
    let mut draws: Vec<Draw> = Vec::new();
    let mut open = false;
    let mut full = false;
    let view = |r: DeviceRect| in_view(r, scroll, w, h);
    for item in &list.items {
        // Room for a balancing pop, always.
        if draws.len().saturating_add(2) >= MAX_DRAWS {
            full = true;
        }
        match item {
            Item::PushClip { rect } => {
                if full {
                    continue;
                }
                let (x, y, width, height) = view(*rect).unwrap_or((0, 0, 0, 0));
                draws.push(Draw::Item(ExecItem::PushClip {
                    x,
                    y,
                    width,
                    height,
                }));
                open = true;
            }
            Item::PopClip => {
                if open {
                    draws.push(Draw::Item(ExecItem::PopClip));
                    open = false;
                }
            }
            Item::Fill { rect, colour } => {
                if full {
                    continue;
                }
                if let Some((x, y, width, height)) = view(*rect) {
                    draws.push(Draw::Item(ExecItem::FillRect {
                        x,
                        y,
                        width,
                        height,
                        colour: *colour,
                    }));
                }
            }
            Item::Text { bounds, run } => {
                if full || view(*bounds).is_none() {
                    continue;
                }
                for g in &run.glyphs {
                    if draws.len().saturating_add(2) >= MAX_DRAWS {
                        full = true;
                        break;
                    }
                    let (px, qx) = split(g.x);
                    let (py, qy) = split(g.y);
                    let key = Key {
                        face: run.face,
                        glyph: g.id,
                        size: run.size,
                        x: quarter_number(qx),
                        y: quarter_number(qy),
                    };
                    let y = i64::from(py).saturating_sub(scroll);
                    // A mask is at most 1,024 px a side: a glyph whose origin is
                    // further than that outside the viewport draws nothing in
                    // it (and keeps every position far inside 5.17a's range).
                    let reach = i64::from(clazel_glyph_mask::MAX_SIDE);
                    let x64 = i64::from(px);
                    if x64 < reach.saturating_neg()
                        || x64 > i64::from(w).saturating_add(reach)
                        || y < reach.saturating_neg()
                        || y > i64::from(h).saturating_add(reach)
                    {
                        continue;
                    }
                    draws.push(Draw::Glyph {
                        key,
                        x: px,
                        y: i32::try_from(y).unwrap_or(i32::MIN),
                        colour: run.colour,
                    });
                }
            }
        }
    }
    if open {
        draws.push(Draw::Item(ExecItem::PopClip));
    }
    // The masks this frame needs that the GPU process does not hold.
    let mut needed: Vec<(Key, clazel_glyph_mask::Mask)> = Vec::new();
    let mut seen: HashMap<Key, ()> = HashMap::new();
    for d in &draws {
        let Draw::Glyph { key, .. } = d else { continue };
        if cache.live.contains_key(key) || cache.empty.contains_key(key) || seen.contains_key(key) {
            continue;
        }
        seen.insert(*key, ());
        let Some(face) = usize::try_from(key.face)
            .ok()
            .and_then(|f| fonts.faces.get(f))
        else {
            cache.empty.insert(*key, ());
            continue;
        };
        let path = glyph_path(face, key.glyph, key.size);
        let offset = Offset {
            x: [Quarter::Zero, Quarter::One, Quarter::Two, Quarter::Three]
                .get(usize::from(key.x))
                .copied()
                .unwrap_or_default(),
            y: [Quarter::Zero, Quarter::One, Quarter::Two, Quarter::Three]
                .get(usize::from(key.y))
                .copied()
                .unwrap_or_default(),
        };
        match glyph_mask(&path, offset) {
            Ok(m) if m.width > 0 && m.height > 0 => needed.push((*key, m)),
            _ => {
                cache.empty.insert(*key, ());
            }
        }
    }
    let mut head: Vec<ExecItem> = Vec::new();
    // Too many new masks for what is live: free those this frame does not
    // draw (`mod.rs`).
    let new_bytes = needed.iter().fold(0u64, |a, (_, m)| {
        a.saturating_add(u64::try_from(m.coverage.len()).unwrap_or(u64::MAX))
    });
    let new_count = u64::try_from(needed.len()).unwrap_or(u64::MAX);
    let over = u64::from(cache.masks.live).saturating_add(new_count)
        > u64::try_from(MAX_MASKS).unwrap_or(u64::MAX)
        || cache.masks.bytes.saturating_add(new_bytes)
            > u64::try_from(MAX_MASK_BYTES).unwrap_or(u64::MAX);
    if over {
        let used: HashMap<Key, ()> = draws
            .iter()
            .filter_map(|d| match d {
                Draw::Glyph { key, .. } => Some((*key, ())),
                Draw::Item(_) => None,
            })
            .collect();
        let unused: Vec<Key> = cache
            .live
            .keys()
            .filter(|k| !used.contains_key(k))
            .copied()
            .collect();
        for k in unused {
            if let Some(l) = cache.live.remove(&k) {
                cache.masks = cache.masks.release(l.id, l.bytes);
                head.push(ExecItem::FreeMask { id: l.id });
            }
        }
    }
    for (key, m) in needed {
        let bytes = u64::try_from(m.coverage.len()).unwrap_or(u64::MAX);
        let (Ok(columns), Ok(rows)) = (u16::try_from(m.width), u16::try_from(m.height)) else {
            continue;
        };
        let Some((next, id)) = cache.masks.allocate(bytes) else {
            // Beyond the limits even so: this glyph is not drawn.
            continue;
        };
        cache.masks = next;
        cache.live.insert(
            key,
            Live {
                id,
                left: m.left,
                top: m.top,
                bytes,
            },
        );
        head.push(ExecItem::UploadMask {
            id,
            columns,
            rows,
            coverage: m.coverage,
        });
    }
    let mut items = head;
    for d in draws {
        match d {
            Draw::Item(i) => items.push(i),
            Draw::Glyph { key, x, y, colour } => {
                if let Some(l) = cache.live.get(&key) {
                    items.push(ExecItem::DrawMask {
                        id: l.id,
                        x: x.saturating_add(l.left),
                        y: y.saturating_add(l.top),
                        colour,
                    });
                }
            }
        }
    }
    items
}

/// `items` encoded (item 5.17a) and framed for the socket: a 4-byte
/// big-endian length, then the list (`state.rs`'s contract); `None` if the
/// list does not encode within 5.17a's limits.
pub fn frame_bytes(items: &[ExecItem]) -> Option<Vec<u8>> {
    let list = encode_list(items)?;
    let len = u32::try_from(list.len()).ok()?;
    let mut out = Vec::with_capacity(list.len().saturating_add(4));
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(&list);
    Some(out)
}
