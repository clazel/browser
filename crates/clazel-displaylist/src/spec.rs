//! The definition of a display list (phase-5.md item 5.17a). The format is ours, not
//! a standard's, so there is nothing to transcribe: this file is the definition, and
//! the theorems in `contract.rs` state its properties.
//!
//! # The bytes
//!
//! A list is its items, one after another, with nothing before, between or after
//! them. An item is one tag byte and its fields, little-endian, of fixed width but
//! for a mask's coverage, whose length its width and height give:
//!
//! | Tag | Item | Fields (bytes) |
//! |-----|------|----------------|
//! | 1 | [`Item::FillRect`] | x (4), y (4), width (4), height (4), colour (4) |
//! | 2 | [`Item::PushClip`] | x (4), y (4), width (4), height (4) |
//! | 3 | [`Item::PopClip`] | |
//! | 4 | [`Item::UploadMask`] | id (4), columns (2), rows (2), coverage (columns × rows) |
//! | 5 | [`Item::DrawMask`] | id (4), x (4), y (4), colour (4) |
//! | 6 | [`Item::FreeMask`] | id (4) |
//!
//! Every byte string has one reading or none, and every list one encoding.
//!
//! # The rules
//!
//! [`validate`] walks a decoded list against the masks that earlier frames left
//! uploaded, and gives the masks this frame leaves. A list that fails is refused
//! whole, and the GPU process ends: only a compromised or buggy renderer sends one.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **No varints, no nesting, not CBOR.** phase-5.md first named RFC 8949 here. Every
//!   field is at a fixed offset, so the reader is a small loop over a flat format, with
//!   no allocation per field, which matters at a list per frame.
//! - **Coordinates are exact in `f32`**, which is what `clazel-gpu`'s vertices hold.
//!   Positions lie within ±[`MAX_COORD`] and sizes within [`MAX_COORD`], so a far edge
//!   lies within ±2^24, every integer of which `f32` holds exactly.
//! - **A colour is premultiplied `0xAARRGGBB`**, in the list as a plain `u32`, with no
//!   rule on it, since every value is a colour.
//! - **Masks are numbered by the renderer from 0**, below [`MAX_MASKS`], so the GPU
//!   process keeps them in a table rather than a map. An id is not reused while its
//!   mask lives, and a mask is never replaced: free it, then upload.
//! - **Limits are stated, and provisional until 5.26 measures them:** [`MAX_LIST_BYTES`],
//!   [`MAX_ITEMS`], [`MAX_CLIP_DEPTH`], [`MAX_MASKS`], [`MAX_MASK_SIDE`] and
//!   [`MAX_MASK_BYTES`]. Between them they bound the GPU process's memory and its work
//!   per list.
//! - **Phase 6's image item is not here.** It gets the next tag when it has a meaning;
//!   until then that tag, like every other, fails to decode.
//! - "Failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The longest list: 128 MiB, in the bytes.
pub const MAX_LIST_BYTES: usize = 134_217_728;

/// The most items in one list.
pub const MAX_ITEMS: usize = 1_048_576;

/// The deepest stack of clips.
pub const MAX_CLIP_DEPTH: usize = 256;

/// How many masks can be alive, so every id is below this.
pub const MAX_MASKS: usize = 65_536;

/// The longest side of a mask, in pixels.
pub const MAX_MASK_SIDE: usize = 2048;

/// The most coverage bytes alive at once: 64 MiB, what the atlas holds.
pub const MAX_MASK_BYTES: usize = 67_108_864;

/// The largest magnitude of a position, and the largest size: 2^23.
pub const MAX_COORD: usize = 8_388_608;

/// One thing to draw, or a change to what later items draw with.
pub ghost enum Item {
    /// Fill a rectangle with a colour, under the current clip.
    FillRect {
        /// The left edge, in device pixels.
        x: i32,
        /// The top edge.
        y: i32,
        /// The width.
        width: u32,
        /// The height.
        height: u32,
        /// Premultiplied `0xAARRGGBB`.
        colour: u32,
    },
    /// Intersect the clip with a rectangle, until the matching [`Item::PopClip`].
    PushClip {
        /// The left edge, in device pixels.
        x: i32,
        /// The top edge.
        y: i32,
        /// The width.
        width: u32,
        /// The height.
        height: u32,
    },
    /// Undo the latest [`Item::PushClip`].
    PopClip,
    /// Keep a glyph's coverage under an id.
    UploadMask {
        /// The renderer's number for it.
        id: u32,
        /// The width in pixels.
        columns: u16,
        /// The height in pixels.
        rows: u16,
        /// `columns × rows` bytes, in rows from the top.
        coverage: Seq<u8>,
    },
    /// Draw a mask with its top left corner at a point, in a colour, under the
    /// current clip.
    DrawMask {
        /// The mask.
        id: u32,
        /// The left edge, in device pixels.
        x: i32,
        /// The top edge.
        y: i32,
        /// Premultiplied `0xAARRGGBB`.
        colour: u32,
    },
    /// Forget a mask, releasing its coverage.
    FreeMask {
        /// The mask.
        id: u32,
    },
}

/// The size of a live mask.
pub ghost struct MaskSize {
    /// The width in pixels.
    pub width: nat,
    /// The height in pixels.
    pub height: nat,
}

/// The masks alive between lists, indexed by id.
pub ghost struct Masks {
    /// One entry per possible id.
    pub table: Seq<Option<MaskSize>>,
}

// ---------------------------------------------------------------- numbers

/// `n` as a sequence of `width` bytes, least significant first.
pub open spec fn le_bytes(n: nat, width: nat) -> Seq<u8>
    decreases width,
{
    if width == 0 {
        Seq::empty()
    } else {
        seq![(n % 256) as u8] + le_bytes(n / 256, (width - 1) as nat)
    }
}

/// The number that a sequence of bytes holds, least significant first.
pub open spec fn le_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] as nat + 256 * le_value(s.subrange(1, s.len() as int))
    }
}

/// A two's complement reading of 32 bits.
pub open spec fn i32_of(n: nat) -> i32 {
    if n < 0x8000_0000 {
        n as i32
    } else {
        (n - 0x1_0000_0000) as i32
    }
}

/// The 32 bits of a signed number.
pub open spec fn bits_of(v: i32) -> nat {
    if v >= 0 {
        v as nat
    } else {
        (v + 0x1_0000_0000) as nat
    }
}

/// Four bytes of `s` from `at`, as a number.
pub open spec fn field4(s: Seq<u8>, at: int) -> nat {
    le_value(s.subrange(at, at + 4))
}

/// Two bytes of `s` from `at`, as a number.
pub open spec fn field2(s: Seq<u8>, at: int) -> nat {
    le_value(s.subrange(at, at + 2))
}

// ---------------------------------------------------------------- encoding

/// Whether an item can be written: a mask's coverage is as long as its sides say.
pub open spec fn encodable(item: Item) -> bool {
    match item {
        Item::UploadMask { columns: width, rows: height, coverage, .. } => coverage.len() == width as nat * height as nat,
        _ => true,
    }
}

/// An item's bytes.
pub open spec fn encode_item(item: Item) -> Seq<u8> {
    match item {
        Item::FillRect { x, y, width, height, colour } => seq![1u8]
            + le_bytes(bits_of(x), 4)
            + le_bytes(bits_of(y), 4)
            + le_bytes(width as nat, 4)
            + le_bytes(height as nat, 4)
            + le_bytes(colour as nat, 4),
        Item::PushClip { x, y, width, height } => seq![2u8]
            + le_bytes(bits_of(x), 4)
            + le_bytes(bits_of(y), 4)
            + le_bytes(width as nat, 4)
            + le_bytes(height as nat, 4),
        Item::PopClip => seq![3u8],
        Item::UploadMask { id, columns: width, rows: height, coverage } => seq![4u8]
            + le_bytes(id as nat, 4)
            + le_bytes(width as nat, 2)
            + le_bytes(height as nat, 2)
            + coverage,
        Item::DrawMask { id, x, y, colour } => seq![5u8]
            + le_bytes(id as nat, 4)
            + le_bytes(bits_of(x), 4)
            + le_bytes(bits_of(y), 4)
            + le_bytes(colour as nat, 4),
        Item::FreeMask { id } => seq![6u8] + le_bytes(id as nat, 4),
    }
}

/// A list's bytes.
pub open spec fn encode(items: Seq<Item>) -> Seq<u8>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        encode_item(items[0]) + encode(items.subrange(1, items.len() as int))
    }
}

// ---------------------------------------------------------------- decoding

/// The item at the start of `s` and how many bytes it takes, or `None` for an unknown
/// tag or too few bytes.
pub open spec fn decode_item(s: Seq<u8>) -> Option<(Item, nat)> {
    if s.len() == 0 {
        None
    } else if s[0] == 1u8 {
        if s.len() < 21 {
            None
        } else {
            Some((
                Item::FillRect {
                    x: i32_of(field4(s, 1)),
                    y: i32_of(field4(s, 5)),
                    width: field4(s, 9) as u32,
                    height: field4(s, 13) as u32,
                    colour: field4(s, 17) as u32,
                },
                21,
            ))
        }
    } else if s[0] == 2u8 {
        if s.len() < 17 {
            None
        } else {
            Some((
                Item::PushClip {
                    x: i32_of(field4(s, 1)),
                    y: i32_of(field4(s, 5)),
                    width: field4(s, 9) as u32,
                    height: field4(s, 13) as u32,
                },
                17,
            ))
        }
    } else if s[0] == 3u8 {
        Some((Item::PopClip, 1))
    } else if s[0] == 4u8 {
        if s.len() < 9 {
            None
        } else {
            let width = field2(s, 5);
            let height = field2(s, 7);
            let size = width * height;
            if s.len() < 9 + size {
                None
            } else {
                Some((
                    Item::UploadMask {
                        id: field4(s, 1) as u32,
                        columns: width as u16,
                        rows: height as u16,
                        coverage: s.subrange(9, 9 + size as int),
                    },
                    9 + size,
                ))
            }
        }
    } else if s[0] == 5u8 {
        if s.len() < 17 {
            None
        } else {
            Some((
                Item::DrawMask {
                    id: field4(s, 1) as u32,
                    x: i32_of(field4(s, 5)),
                    y: i32_of(field4(s, 9)),
                    colour: field4(s, 13) as u32,
                },
                17,
            ))
        }
    } else if s[0] == 6u8 {
        if s.len() < 5 {
            None
        } else {
            Some((Item::FreeMask { id: field4(s, 1) as u32 }, 5))
        }
    } else {
        None
    }
}

/// The items of `s`, however many. Every item takes at least one byte and no more than
/// are left, so the guard on `taken` never fails (a lemma); it is what shows this ends.
pub open spec fn decode_items(s: Seq<u8>) -> Option<Seq<Item>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match decode_item(s) {
            None => None,
            Some((item, taken)) => {
                if 0 < taken <= s.len() {
                    match decode_items(s.subrange(taken as int, s.len() as int)) {
                        None => None,
                        Some(rest) => Some(seq![item] + rest),
                    }
                } else {
                    None
                }
            },
        }
    }
}

/// A list's items, or `None` if it is too long or is not exactly a run of items.
pub open spec fn decode(s: Seq<u8>) -> Option<Seq<Item>> {
    if s.len() > (MAX_LIST_BYTES as nat) {
        None
    } else {
        decode_items(s)
    }
}

// ---------------------------------------------------------------- the rules

/// A position `clazel-gpu` can hold.
pub open spec fn position_ok(v: i32) -> bool {
    -(MAX_COORD as int) <= v as int <= MAX_COORD as int
}

/// A size `clazel-gpu` can hold.
pub open spec fn size_ok(v: u32) -> bool {
    v as nat <= (MAX_COORD as nat)
}

/// No masks.
pub open spec fn no_masks() -> Masks {
    Masks { table: Seq::new((MAX_MASKS as nat), |i: int| None) }
}

/// The table has its fixed length.
pub open spec fn masks_ok(masks: Masks) -> bool {
    masks.table.len() == (MAX_MASKS as nat) && live_bytes(masks.table) <= (MAX_MASK_BYTES as nat)
}

/// The coverage bytes of every live mask in a table.
pub open spec fn live_bytes(table: Seq<Option<MaskSize>>) -> nat
    decreases table.len(),
{
    if table.len() == 0 {
        0
    } else {
        let rest = live_bytes(table.subrange(1, table.len() as int));
        match table[0] {
            None => rest,
            Some(size) => size.width * size.height + rest,
        }
    }
}

/// Whether `id` names a live mask.
pub open spec fn is_live(masks: Masks, id: u32) -> bool {
    (id as nat) < (MAX_MASKS as nat) && masks.table[id as int] is Some
}

/// The masks after one item, or `None` if the item breaks a rule. Clips are
/// [`clip_after`]'s, since they do not outlive the list.
pub open spec fn masks_after(masks: Masks, item: Item) -> Option<Masks> {
    match item {
        Item::FillRect { x, y, width, height, .. } => {
            if position_ok(x) && position_ok(y) && size_ok(width) && size_ok(height) {
                Some(masks)
            } else {
                None
            }
        },
        Item::PushClip { x, y, width, height } => {
            if position_ok(x) && position_ok(y) && size_ok(width) && size_ok(height) {
                Some(masks)
            } else {
                None
            }
        },
        Item::PopClip => Some(masks),
        Item::UploadMask { id, columns: width, rows: height, .. } => {
            let size = MaskSize { width: width as nat, height: height as nat };
            let updated = Masks { table: masks.table.update(id as int, Some(size)) };
            if id as nat >= (MAX_MASKS as nat) || masks.table[id as int] is Some {
                None
            } else if width == 0 || height == 0 {
                None
            } else if width as nat > (MAX_MASK_SIDE as nat) || height as nat > (MAX_MASK_SIDE as nat) {
                None
            } else if live_bytes(updated.table) > (MAX_MASK_BYTES as nat) {
                None
            } else {
                Some(updated)
            }
        },
        Item::DrawMask { id, x, y, .. } => {
            if position_ok(x) && position_ok(y) && is_live(masks, id) {
                Some(masks)
            } else {
                None
            }
        },
        Item::FreeMask { id } => {
            if is_live(masks, id) {
                Some(Masks { table: masks.table.update(id as int, None) })
            } else {
                None
            }
        },
    }
}

/// The depth of the clip stack after one item, or `None` if it would pass
/// [`MAX_CLIP_DEPTH`] or pop an empty stack.
pub open spec fn clip_after(depth: nat, item: Item) -> Option<nat> {
    match item {
        Item::PushClip { .. } => {
            if depth < (MAX_CLIP_DEPTH as nat) {
                Some(depth + 1)
            } else {
                None
            }
        },
        Item::PopClip => {
            if depth > 0 {
                Some((depth - 1) as nat)
            } else {
                None
            }
        },
        _ => Some(depth),
    }
}

/// The masks after a run of items at a clip depth, or `None` if an item breaks a rule
/// or clips are still pushed at the end.
pub open spec fn walk(masks: Masks, depth: nat, items: Seq<Item>) -> Option<Masks>
    decreases items.len(),
{
    if items.len() == 0 {
        if depth == 0 {
            Some(masks)
        } else {
            None
        }
    } else {
        match (masks_after(masks, items[0]), clip_after(depth, items[0])) {
            (Some(next_masks), Some(next_depth)) => walk(next_masks, next_depth, items.subrange(1, items.len() as int)),
            _ => None,
        }
    }
}

/// The masks a list leaves, given those it found, or `None` if the list is refused.
pub open spec fn validate(masks: Masks, items: Seq<Item>) -> Option<Masks> {
    if items.len() > (MAX_ITEMS as nat) {
        None
    } else {
        walk(masks, 0, items)
    }
}

// ---------------------------------------------------------------- what a list means

/// The rule `clazel-gpu` relies on for one item, said without reference to the walk:
/// every number it reads is in range.
pub open spec fn in_range(item: Item) -> bool {
    match item {
        Item::FillRect { x, y, width, height, .. } => position_ok(x) && position_ok(y) && size_ok(width) && size_ok(height),
        Item::PushClip { x, y, width, height } => position_ok(x) && position_ok(y) && size_ok(width) && size_ok(height),
        Item::PopClip => true,
        Item::UploadMask { id, columns: width, rows: height, .. } => {
            (id as nat) < (MAX_MASKS as nat)
                && 0 < width as nat <= (MAX_MASK_SIDE as nat)
                && 0 < height as nat <= (MAX_MASK_SIDE as nat)
        },
        Item::DrawMask { id, x, y, .. } => (id as nat) < (MAX_MASKS as nat) && position_ok(x) && position_ok(y),
        Item::FreeMask { id } => (id as nat) < (MAX_MASKS as nat),
    }
}

/// The clip depth after the first `n` items, ignoring limits. A second statement of
/// [`clip_after`], as a count, for the theorem that clips balance.
pub open spec fn depth_at(items: Seq<Item>, n: nat) -> int
    decreases n,
{
    if n == 0 || n > items.len() {
        0
    } else {
        depth_at(items, (n - 1) as nat) + match items[n - 1] {
            Item::PushClip { .. } => 1int,
            Item::PopClip => -1int,
            _ => 0int,
        }
    }
}

} // verus!
