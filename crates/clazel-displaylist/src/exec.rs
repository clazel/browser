//! The executable encoder, decoder and validator, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`Item`], in memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecItem {
    /// [`Item::FillRect`].
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
    /// [`Item::PushClip`].
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
    /// [`Item::PopClip`].
    PopClip,
    /// [`Item::UploadMask`].
    UploadMask {
        /// The renderer's number for it.
        id: u32,
        /// The width in pixels.
        columns: u16,
        /// The height in pixels.
        rows: u16,
        /// `columns × rows` bytes, in rows from the top.
        coverage: Vec<u8>,
    },
    /// [`Item::DrawMask`].
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
    /// [`Item::FreeMask`].
    FreeMask {
        /// The mask.
        id: u32,
    },
    /// [`Item::UploadImage`].
    UploadImage {
        /// The renderer's number for it, in the images' own space.
        id: u32,
        /// The width in pixels.
        image_width: u16,
        /// The height in pixels.
        image_height: u16,
        /// `width × height × 4` bytes of premultiplied RGBA8, in rows from the top.
        pixels: Vec<u8>,
    },
    /// [`Item::DrawImage`].
    DrawImage {
        /// The image.
        id: u32,
        /// The destination's left edge, in device pixels.
        x: i32,
        /// The destination's top edge.
        y: i32,
        /// The destination's width.
        width: u32,
        /// The destination's height.
        height: u32,
        /// The source's left edge, in the image's pixels.
        src_x: u16,
        /// The source's top edge.
        src_y: u16,
        /// The source's width.
        src_width: u16,
        /// The source's height.
        src_height: u16,
        /// Linear filtering if true, nearest if false.
        linear: bool,
    },
    /// [`Item::FreeImage`].
    FreeImage {
        /// The image.
        id: u32,
    },
}

/// The item a [`ExecItem`] holds.
pub open spec fn view_item(item: ExecItem) -> Item {
    match item {
        ExecItem::FillRect { x, y, width, height, colour } => Item::FillRect { x, y, width, height, colour },
        ExecItem::PushClip { x, y, width, height } => Item::PushClip { x, y, width, height },
        ExecItem::PopClip => Item::PopClip,
        ExecItem::UploadMask { id, columns, rows, coverage } => Item::UploadMask { id, columns, rows, coverage: coverage@ },
        ExecItem::DrawMask { id, x, y, colour } => Item::DrawMask { id, x, y, colour },
        ExecItem::FreeMask { id } => Item::FreeMask { id },
        ExecItem::UploadImage { id, image_width: width, image_height: height, pixels } => Item::UploadImage { id, image_width: width, image_height: height, pixels: pixels@ },
        ExecItem::DrawImage { id, x, y, width, height, src_x, src_y, src_width, src_height, linear } => Item::DrawImage {
            id,
            x,
            y,
            width,
            height,
            src_x,
            src_y,
            src_width,
            src_height,
            linear,
        },
        ExecItem::FreeImage { id } => Item::FreeImage { id },
    }
}

/// The items a slice holds.
pub open spec fn view_items(items: Seq<ExecItem>) -> Seq<Item> {
    items.map_values(|item: ExecItem| view_item(item))
}

/// The bytes a [`encode`]'s result holds.
pub open spec fn view_bytes(output: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match output {
        Some(v) => Some(v@),
        None => None,
    }
}

/// The items a [`decode`]'s result holds.
pub open spec fn view_list(output: Option<Vec<ExecItem>>) -> Option<Seq<Item>> {
    match output {
        Some(v) => Some(view_items(v@)),
        None => None,
    }
}

// ---------------------------------------------------------------- reading

/// `width` bytes of `input` from `pos`, as a number.
fn read_le(input: &[u8], pos: usize, width: usize) -> (value: u64)
    requires
        width <= 4,
        pos + width <= input.len(),
    ensures
        value as nat == le_value(input@.subrange(pos as int, pos as int + width as int)),
        (value as nat) < super::lemmas::pow256(width as nat),
    decreases width,
{
    proof {
        super::lemmas::lemma_pow256_values();
    }
    if width == 0 {
        assert(input@.subrange(pos as int, pos as int) =~= Seq::<u8>::empty());
        return 0;
    }
    let ghost whole = input@.subrange(pos as int, pos as int + width as int);
    let ghost rest = input@.subrange(pos as int + 1, pos as int + width as int);
    assert(whole.subrange(1, whole.len() as int) =~= rest);
    // Neither saturates: width >= 1, and pos + width <= input.len().
    let high = read_le(input, pos.saturating_add(1), width.saturating_sub(1));
    let low = match input.get(pos) {
        Some(&b) => b,
        None => 0,
    };
    proof {
        super::lemmas::lemma_le_value_bound(whole);
        assert(super::lemmas::pow256(width as nat) == 256 * super::lemmas::pow256((width - 1) as nat));
        assert(super::lemmas::pow256(width as nat) <= 0x1_0000_0000nat) by {
            assert(width == 1 || width == 2 || width == 3 || width == 4);
        }
        assert(le_value(whole) == low as nat + 256 * high as nat);
        assert(256 * high as nat <= 0x1_0000_0000nat);
    }
    // Neither saturates, by the bound above.
    high.saturating_mul(256).saturating_add(low as u64)
}

/// [`i32_of`].
fn i32_from(n: u64) -> (value: i32)
    requires
        n < 0x1_0000_0000,
    ensures
        value == i32_of(n as nat),
{
    if n < 0x8000_0000 {
        n as i32
    } else {
        // n is below 2^32, so this is at least -2^31, and it does not overflow.
        match (n as i64).checked_sub(0x1_0000_0000i64) {
            Some(v) => v as i32,
            None => 0,
        }
    }
}

/// The item at `pos` and the bytes it takes: [`decode_item`] of what is left.
fn decode_item_at(bytes: &[u8], pos: usize) -> (output: Option<(ExecItem, usize)>)
    requires
        pos <= bytes.len(),
    ensures
        match output {
            None => decode_item(bytes@.subrange(pos as int, bytes.len() as int)) is None,
            Some((item, taken)) => decode_item(bytes@.subrange(pos as int, bytes.len() as int)) == Some(
                (view_item(item), taken as nat),
            ),
        },
{
    let ghost s = bytes@.subrange(pos as int, bytes.len() as int);
    proof {
        super::lemmas::lemma_pow256_values();
    }
    // pos <= bytes.len(), so this is exact.
    let left = bytes.len().saturating_sub(pos);
    let tag = match bytes.get(pos) {
        Some(&b) => b,
        None => {
            return None;
        },
    };
    assert(s[0] == tag);
    // Every addition below is within bytes.len(), by the length tests.
    if tag == 1 {
        if left < 21 {
            return None;
        }
        let x = read_le(bytes, pos.saturating_add(1), 4);
        let y = read_le(bytes, pos.saturating_add(5), 4);
        let width = read_le(bytes, pos.saturating_add(9), 4);
        let height = read_le(bytes, pos.saturating_add(13), 4);
        let colour = read_le(bytes, pos.saturating_add(17), 4);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 9) =~= bytes@.subrange(pos + 5, pos + 9));
        assert(s.subrange(9, 13) =~= bytes@.subrange(pos + 9, pos + 13));
        assert(s.subrange(13, 17) =~= bytes@.subrange(pos + 13, pos + 17));
        assert(s.subrange(17, 21) =~= bytes@.subrange(pos + 17, pos + 21));
        let item = ExecItem::FillRect {
            x: i32_from(x),
            y: i32_from(y),
            width: width as u32,
            height: height as u32,
            colour: colour as u32,
        };
        Some((item, 21))
    } else if tag == 2 {
        if left < 17 {
            return None;
        }
        let x = read_le(bytes, pos.saturating_add(1), 4);
        let y = read_le(bytes, pos.saturating_add(5), 4);
        let width = read_le(bytes, pos.saturating_add(9), 4);
        let height = read_le(bytes, pos.saturating_add(13), 4);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 9) =~= bytes@.subrange(pos + 5, pos + 9));
        assert(s.subrange(9, 13) =~= bytes@.subrange(pos + 9, pos + 13));
        assert(s.subrange(13, 17) =~= bytes@.subrange(pos + 13, pos + 17));
        let item = ExecItem::PushClip {
            x: i32_from(x),
            y: i32_from(y),
            width: width as u32,
            height: height as u32,
        };
        Some((item, 17))
    } else if tag == 3 {
        Some((ExecItem::PopClip, 1))
    } else if tag == 4 {
        if left < 9 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        let columns = read_le(bytes, pos.saturating_add(5), 2);
        let rows = read_le(bytes, pos.saturating_add(7), 2);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 7) =~= bytes@.subrange(pos + 5, pos + 7));
        assert(s.subrange(7, 9) =~= bytes@.subrange(pos + 7, pos + 9));
        assert(columns * rows < 0x1_0000_0000) by (nonlinear_arith)
            requires
                columns < 65536,
                rows < 65536,
        ;
        // Does not saturate, by the bound above.
        let size = columns.saturating_mul(rows);
        // left - 9 is exact: left >= 9.
        if (left.saturating_sub(9) as u64) < size {
            return None;
        }
        let start = pos.saturating_add(9);
        // Within bytes.len(): size <= left - 9.
        let end = start.saturating_add(size as usize);
        let coverage = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(bytes, start, end));
        assert(s.subrange(9, 9 + size as int) =~= bytes@.subrange(start as int, end as int));
        let item = ExecItem::UploadMask { id: id as u32, columns: columns as u16, rows: rows as u16, coverage };
        // 9 + size <= left, which is a usize.
        Some((item, (size as usize).saturating_add(9)))
    } else if tag == 5 {
        if left < 17 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        let x = read_le(bytes, pos.saturating_add(5), 4);
        let y = read_le(bytes, pos.saturating_add(9), 4);
        let colour = read_le(bytes, pos.saturating_add(13), 4);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 9) =~= bytes@.subrange(pos + 5, pos + 9));
        assert(s.subrange(9, 13) =~= bytes@.subrange(pos + 9, pos + 13));
        assert(s.subrange(13, 17) =~= bytes@.subrange(pos + 13, pos + 17));
        let item = ExecItem::DrawMask {
            id: id as u32,
            x: i32_from(x),
            y: i32_from(y),
            colour: colour as u32,
        };
        Some((item, 17))
    } else if tag == 6 {
        if left < 5 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        Some((ExecItem::FreeMask { id: id as u32 }, 5))
    } else if tag == 7 {
        // 6.10 "upload image (id, width, height, then width × height × 4 bytes ...)".
        if left < 9 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        let width = read_le(bytes, pos.saturating_add(5), 2);
        let height = read_le(bytes, pos.saturating_add(7), 2);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 7) =~= bytes@.subrange(pos + 5, pos + 7));
        assert(s.subrange(7, 9) =~= bytes@.subrange(pos + 7, pos + 9));
        assert(width * height * 4 < 0x4_0000_0000) by (nonlinear_arith)
            requires
                width < 65536,
                height < 65536,
        ;
        // Neither saturates, by the bound above.
        let size = width.saturating_mul(height).saturating_mul(4);
        // left - 9 is exact: left >= 9.
        if (left.saturating_sub(9) as u64) < size {
            return None;
        }
        let start = pos.saturating_add(9);
        // Within bytes.len(): size <= left - 9.
        let end = start.saturating_add(size as usize);
        let pixels = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(bytes, start, end));
        assert(s.subrange(9, 9 + size as int) =~= bytes@.subrange(start as int, end as int));
        let item = ExecItem::UploadImage { id: id as u32, image_width: width as u16, image_height: height as u16, pixels };
        // 9 + size <= left, which is a usize.
        Some((item, (size as usize).saturating_add(9)))
    } else if tag == 8 {
        // 6.10 "draw image (id, destination x, y, width, height, as tag 1; source
        // rectangle in the image's pixels; a filter flag, nearest or linear)".
        if left < 30 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        let x = read_le(bytes, pos.saturating_add(5), 4);
        let y = read_le(bytes, pos.saturating_add(9), 4);
        let width = read_le(bytes, pos.saturating_add(13), 4);
        let height = read_le(bytes, pos.saturating_add(17), 4);
        let src_x = read_le(bytes, pos.saturating_add(21), 2);
        let src_y = read_le(bytes, pos.saturating_add(23), 2);
        let src_width = read_le(bytes, pos.saturating_add(25), 2);
        let src_height = read_le(bytes, pos.saturating_add(27), 2);
        let filter = match bytes.get(pos.saturating_add(29)) {
            Some(&b) => b,
            None => {
                return None;
            },
        };
        assert(s[29] == filter);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        assert(s.subrange(5, 9) =~= bytes@.subrange(pos + 5, pos + 9));
        assert(s.subrange(9, 13) =~= bytes@.subrange(pos + 9, pos + 13));
        assert(s.subrange(13, 17) =~= bytes@.subrange(pos + 13, pos + 17));
        assert(s.subrange(17, 21) =~= bytes@.subrange(pos + 17, pos + 21));
        assert(s.subrange(21, 23) =~= bytes@.subrange(pos + 21, pos + 23));
        assert(s.subrange(23, 25) =~= bytes@.subrange(pos + 23, pos + 25));
        assert(s.subrange(25, 27) =~= bytes@.subrange(pos + 25, pos + 27));
        assert(s.subrange(27, 29) =~= bytes@.subrange(pos + 27, pos + 29));
        if filter != 0 && filter != 1 {
            return None;
        }
        let item = ExecItem::DrawImage {
            id: id as u32,
            x: i32_from(x),
            y: i32_from(y),
            width: width as u32,
            height: height as u32,
            src_x: src_x as u16,
            src_y: src_y as u16,
            src_width: src_width as u16,
            src_height: src_height as u16,
            linear: filter == 1,
        };
        Some((item, 30))
    } else if tag == 9 {
        if left < 5 {
            return None;
        }
        let id = read_le(bytes, pos.saturating_add(1), 4);
        assert(s.subrange(1, 5) =~= bytes@.subrange(pos + 1, pos + 5));
        Some((ExecItem::FreeImage { id: id as u32 }, 5))
    } else {
        None
    }
}

/// `items`, then `rest` if there is one.
spec fn prepend(items: Seq<Item>, rest: Option<Seq<Item>>) -> Option<Seq<Item>> {
    match rest {
        None => None,
        Some(tail) => Some(items + tail),
    }
}

/// The decoder: a list's items, or `None` if it is too long or not exactly a run of
/// items. It iterates, so a long list cannot overflow the stack.
pub fn decode(bytes: &[u8]) -> (output: Option<Vec<ExecItem>>)
    ensures
        super::contract::decode_ensures(bytes@, view_list(output)),
{
    if bytes.len() > MAX_LIST_BYTES {
        return None;
    }
    let mut items: Vec<ExecItem> = Vec::new();
    let mut pos: usize = 0;
    assert(bytes@.subrange(0, bytes@.len() as int) =~= bytes@);
    assert(view_items(items@) =~= Seq::<Item>::empty());
    assert(Seq::<Item>::empty() + decode_items(bytes@)->Some_0 =~= decode_items(bytes@)->Some_0);
    while pos < bytes.len()
        invariant
            pos <= bytes.len(),
            bytes.len() <= MAX_LIST_BYTES,
            decode_items(bytes@) == prepend(
                view_items(items@),
                decode_items(bytes@.subrange(pos as int, bytes.len() as int)),
            ),
        decreases bytes.len() - pos,
    {
        let ghost s = bytes@.subrange(pos as int, bytes.len() as int);
        let ghost before = view_items(items@);
        let (item, taken) = match decode_item_at(bytes, pos) {
            Some(found) => found,
            None => {
                assert(decode_items(s) is None);
                return None;
            },
        };
        proof {
            super::lemmas::lemma_decode_item_sound(s);
        }
        let ghost suffix = s.subrange(taken as int, s.len() as int);
        let ghost next = bytes@.subrange(pos + taken, bytes.len() as int);
        assert(suffix =~= next);
        let ghost one = view_item(item);
        items.push(item);
        // taken <= s.len(), so this stays within bytes.len().
        pos = pos.saturating_add(taken);
        proof {
            assert(view_items(items@) =~= before.push(one));
            match decode_items(next) {
                None => {},
                Some(tail) => {
                    assert(before.push(one) + tail =~= before + (seq![one] + tail));
                },
            }
        }
    }
    proof {
        assert(bytes@.subrange(pos as int, bytes.len() as int) =~= Seq::<u8>::empty());
        assert(view_items(items@) + Seq::<Item>::empty() =~= view_items(items@));
    }
    Some(items)
}

// ---------------------------------------------------------------- writing

/// Append [`le_bytes`].
fn push_le(out: &mut Vec<u8>, value: u64, width: usize)
    ensures
        final(out)@ == old(out)@ + le_bytes(value as nat, width as nat),
    decreases width,
{
    if width == 0 {
        assert(old(out)@ + le_bytes(value as nat, 0) =~= old(out)@);
        return;
    }
    out.push((value % 256) as u8);
    let ghost pushed = out@;
    // Does not saturate: width >= 1.
    push_le(out, value / 256, width.saturating_sub(1));
    assert(out@ =~= old(out)@ + le_bytes(value as nat, width as nat));
}

/// [`bits_of`].
fn bits(v: i32) -> (value: u64)
    ensures
        value as nat == bits_of(v),
{
    if v >= 0 {
        v as u64
    } else {
        // v is at least -2^31, so this is positive, and it does not overflow.
        match (v as i64).checked_add(0x1_0000_0000i64) {
            Some(sum) => sum as u64,
            None => 0,
        }
    }
}

/// Append [`encode_item`].
fn push_item(out: &mut Vec<u8>, item: &ExecItem)
    ensures
        final(out)@ == old(out)@ + encode_item(view_item(*item)),
{
    let ghost start = out@;
    match item {
        ExecItem::FillRect { x, y, width, height, colour } => {
            out.push(1);
            push_le(out, bits(*x), 4);
            push_le(out, bits(*y), 4);
            push_le(out, *width as u64, 4);
            push_le(out, *height as u64, 4);
            push_le(out, *colour as u64, 4);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::PushClip { x, y, width, height } => {
            out.push(2);
            push_le(out, bits(*x), 4);
            push_le(out, bits(*y), 4);
            push_le(out, *width as u64, 4);
            push_le(out, *height as u64, 4);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::PopClip => {
            out.push(3);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::UploadMask { id, columns, rows, coverage } => {
            out.push(4);
            push_le(out, *id as u64, 4);
            push_le(out, *columns as u64, 2);
            push_le(out, *rows as u64, 2);
            out.extend_from_slice(coverage.as_slice());
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::DrawMask { id, x, y, colour } => {
            out.push(5);
            push_le(out, *id as u64, 4);
            push_le(out, bits(*x), 4);
            push_le(out, bits(*y), 4);
            push_le(out, *colour as u64, 4);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::FreeMask { id } => {
            out.push(6);
            push_le(out, *id as u64, 4);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::UploadImage { id, image_width: width, image_height: height, pixels } => {
            out.push(7);
            push_le(out, *id as u64, 4);
            push_le(out, *width as u64, 2);
            push_le(out, *height as u64, 2);
            out.extend_from_slice(pixels.as_slice());
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::DrawImage { id, x, y, width, height, src_x, src_y, src_width, src_height, linear } => {
            out.push(8);
            push_le(out, *id as u64, 4);
            push_le(out, bits(*x), 4);
            push_le(out, bits(*y), 4);
            push_le(out, *width as u64, 4);
            push_le(out, *height as u64, 4);
            push_le(out, *src_x as u64, 2);
            push_le(out, *src_y as u64, 2);
            push_le(out, *src_width as u64, 2);
            push_le(out, *src_height as u64, 2);
            out.push(if *linear { 1 } else { 0 });
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
        ExecItem::FreeImage { id } => {
            out.push(9);
            push_le(out, *id as u64, 4);
            assert(out@ =~= start + encode_item(view_item(*item)));
        },
    }
}

/// [`encodable`].
fn can_write(item: &ExecItem) -> (ok: bool)
    ensures
        ok == encodable(view_item(*item)),
{
    match item {
        ExecItem::UploadMask { columns, rows, coverage, .. } => {
            assert((*columns as nat) * (*rows as nat) < 0x1_0000_0000) by (nonlinear_arith)
                requires
                    (*columns as nat) < 65536,
                    (*rows as nat) < 65536,
            ;
            // Does not saturate, by the bound above.
            (coverage.len() as u64) == (*columns as u64).saturating_mul(*rows as u64)
        },
        ExecItem::UploadImage { image_width: width, image_height: height, pixels, .. } => {
            assert((*width as nat) * (*height as nat) * 4 < 0x4_0000_0000) by (nonlinear_arith)
                requires
                    (*width as nat) < 65536,
                    (*height as nat) < 65536,
            ;
            // Neither saturates, by the bound above.
            (pixels.len() as u64) == (*width as u64).saturating_mul(*height as u64).saturating_mul(4)
        },
        _ => true,
    }
}

/// Writing one more item adds its bytes to the end.
proof fn lemma_encode_push(items: Seq<Item>, item: Item)
    ensures
        encode(items.push(item)) =~= encode(items) + encode_item(item),
    decreases items.len(),
{
    if items.len() == 0 {
        let one = items.push(item);
        assert(one.subrange(1, one.len() as int) =~= Seq::<Item>::empty());
        assert(encode(Seq::<Item>::empty()) =~= Seq::<u8>::empty());
    } else {
        let tail = items.subrange(1, items.len() as int);
        let longer = items.push(item);
        assert(longer.subrange(1, longer.len() as int) =~= tail.push(item));
        lemma_encode_push(tail, item);
    }
}

/// The encoder: `None` exactly when an item cannot be written.
pub fn encode_list(items: &[ExecItem]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::encode_ensures(view_items(items@), view_bytes(output)),
{
    let ghost all = view_items(items@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(all.subrange(0, 0) =~= Seq::<Item>::empty());
    assert(encode(Seq::<Item>::empty()) =~= Seq::<u8>::empty());
    while i < items.len()
        invariant
            i <= items.len(),
            all == view_items(items@),
            out@ == encode(all.subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> encodable(#[trigger] all[j]),
        decreases items.len() - i,
    {
        let item = match items.get(i) {
            Some(item) => item,
            None => {
                return None;
            },
        };
        assert(view_item(*item) == all[i as int]);
        if !can_write(item) {
            assert(!encodable(all[i as int]));
            assert(!super::contract::all_encodable(all));
            return None;
        }
        let ghost before = all.subrange(0, i as int);
        push_item(&mut out, item);
        proof {
            lemma_encode_push(before, all[i as int]);
            assert(all.subrange(0, i + 1) =~= before.push(all[i as int]));
        }
        // i < items.len(), so this does not saturate.
        i = i.saturating_add(1);
    }
    assert(all.subrange(0, i as int) =~= all);
    Some(out)
}

// ---------------------------------------------------------------- the rules

/// [`position_ok`].
fn position_is_ok(v: i32) -> (ok: bool)
    ensures
        ok == position_ok(v),
{
    if v < -8_388_608 {
        false
    } else {
        v <= 8_388_608
    }
}

/// [`size_ok`].
fn size_is_ok(v: u32) -> (ok: bool)
    ensures
        ok == size_ok(v),
{
    v <= 8_388_608
}

/// The entry an exec table holds.
pub open spec fn view_entry(entry: Option<(u16, u16)>) -> Option<MaskSize> {
    match entry {
        None => None,
        Some((width, height)) => Some(MaskSize { width: width as nat, height: height as nat }),
    }
}

/// The entry an exec table of images holds.
pub open spec fn view_image_entry(entry: Option<(u16, u16)>) -> Option<ImageSize> {
    match entry {
        None => None,
        Some((width, height)) => Some(ImageSize { width: width as nat, height: height as nat }),
    }
}

/// The validator, which keeps the masks and images between lists.
#[derive(Debug)]
pub struct Validator {
    table: Vec<Option<(u16, u16)>>,
    live: u64,
    images: Vec<Option<(u16, u16)>>,
    image_live: u64,
}

impl Validator {
    /// The masks and images it holds.
    pub closed spec fn masks(&self) -> Masks {
        Masks {
            table: self.table@.map_values(|entry: Option<(u16, u16)>| view_entry(entry)),
            images: self.images@.map_values(|entry: Option<(u16, u16)>| view_image_entry(entry)),
        }
    }

    /// It holds sound tables, and its counts of the coverage bytes and of the pixel
    /// bytes are right.
    pub closed spec fn wf(&self) -> bool {
        &&& masks_ok(self.masks())
        &&& self.live as nat == live_bytes(self.masks().table)
        &&& self.image_live as nat == live_image_bytes(self.masks().images)
    }

    /// A validator with no masks.
    pub fn empty() -> (out: Validator)
        ensures
            out.wf(),
            out.masks() == no_masks(),
    {
        let mut table: Vec<Option<(u16, u16)>> = Vec::new();
        let mut i: usize = 0;
        while i < MAX_MASKS
            invariant
                i <= MAX_MASKS,
                table@.len() == i,
                forall|j: int| 0 <= j < i ==> table@[j] is None,
            decreases MAX_MASKS - i,
        {
            table.push(None);
            // i < MAX_MASKS, so this does not saturate.
            i = i.saturating_add(1);
        }
        let mut images: Vec<Option<(u16, u16)>> = Vec::new();
        let mut j: usize = 0;
        while j < MAX_IMAGES
            invariant
                j <= MAX_IMAGES,
                images@.len() == j,
                forall|k: int| 0 <= k < j ==> images@[k] is None,
            decreases MAX_IMAGES - j,
        {
            images.push(None);
            // j < MAX_IMAGES, so this does not saturate.
            j = j.saturating_add(1);
        }
        let out = Validator { table, live: 0, images, image_live: 0 };
        proof {
            assert(out.masks().table =~= no_masks().table);
            assert(out.masks().images =~= no_masks().images);
            super::lemmas::theorem_no_masks_ok();
            super::lemmas::lemma_live_bytes_none(no_masks().table);
            super::lemmas::lemma_live_image_bytes_none(no_masks().images);
        }
        out
    }

    /// Apply one item at a clip depth, giving the next depth, or `None` if it breaks a
    /// rule. On `None`, the table is unchanged.
    fn step(&mut self, item: &ExecItem, depth: usize) -> (next: Option<usize>)
        requires
            old(self).wf(),
            depth <= MAX_CLIP_DEPTH,
        ensures
            final(self).wf(),
            match next {
                Some(d) => {
                    &&& masks_after(old(self).masks(), view_item(*item)) == Some(final(self).masks())
                    &&& clip_after(depth as nat, view_item(*item)) == Some(d as nat)
                    &&& d <= MAX_CLIP_DEPTH
                },
                None => masks_after(old(self).masks(), view_item(*item)) is None || clip_after(
                    depth as nat,
                    view_item(*item),
                ) is None,
            },
    {
        match item {
            ExecItem::FillRect { x, y, width, height, .. } => {
                if position_is_ok(*x) && position_is_ok(*y) && size_is_ok(*width) && size_is_ok(*height) {
                    Some(depth)
                } else {
                    None
                }
            },
            ExecItem::PushClip { x, y, width, height } => {
                if !(position_is_ok(*x) && position_is_ok(*y) && size_is_ok(*width) && size_is_ok(*height)) {
                    return None;
                }
                if depth < MAX_CLIP_DEPTH {
                    // depth < MAX_CLIP_DEPTH, so this does not saturate.
                    Some(depth.saturating_add(1))
                } else {
                    None
                }
            },
            ExecItem::PopClip => {
                if depth > 0 {
                    // depth > 0, so this is exact.
                    Some(depth.saturating_sub(1))
                } else {
                    None
                }
            },
            ExecItem::UploadMask { id, columns, rows, .. } => {
                let ghost before = self.masks();
                let index = *id as usize;
                if index >= MAX_MASKS {
                    return None;
                }
                let slot = match self.table.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(before.table[index as int] == view_entry(slot));
                if slot.is_some() {
                    return None;
                }
                if *columns == 0 || *rows == 0 {
                    return None;
                }
                if *columns as usize > MAX_MASK_SIDE || *rows as usize > MAX_MASK_SIDE {
                    return None;
                }
                let ghost size = MaskSize { width: *columns as nat, height: *rows as nat };
                proof {
                    super::lemmas::lemma_live_bytes_update(before.table, index as int, Some(size));
                    assert(size.width * size.height <= 4_194_304) by (nonlinear_arith)
                        requires
                            size.width <= 2048,
                            size.height <= 2048,
                    ;
                }
                // Neither saturates: the cost is at most 2^22 and live at most 2^26.
                let cost = (*columns as u64).saturating_mul(*rows as u64);
                let total = self.live.saturating_add(cost);
                if total > MAX_MASK_BYTES as u64 {
                    return None;
                }
                self.table.set(index, Some((*columns, *rows)));
                self.live = total;
                proof {
                    assert(self.masks().table =~= before.table.update(index as int, Some(size)));
                    assert(self.masks().images =~= before.images);
                }
                Some(depth)
            },
            ExecItem::DrawMask { id, x, y, .. } => {
                if !(position_is_ok(*x) && position_is_ok(*y)) {
                    return None;
                }
                let index = *id as usize;
                if index >= MAX_MASKS {
                    return None;
                }
                let slot = match self.table.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(self.masks().table[index as int] == view_entry(slot));
                if slot.is_some() {
                    Some(depth)
                } else {
                    None
                }
            },
            ExecItem::FreeMask { id } => {
                let ghost before = self.masks();
                let index = *id as usize;
                if index >= MAX_MASKS {
                    return None;
                }
                let slot = match self.table.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(before.table[index as int] == view_entry(slot));
                let (columns, rows) = match slot {
                    Some(sides) => sides,
                    None => {
                        return None;
                    },
                };
                proof {
                    super::lemmas::lemma_live_bytes_update(before.table, index as int, None);
                }
                // The freed mask's bytes are part of live, so this is exact, and the
                // product does not saturate: both sides are below 2^16.
                assert((columns as nat) * (rows as nat) < 0x1_0000_0000) by (nonlinear_arith)
                    requires
                        (columns as nat) < 65536,
                        (rows as nat) < 65536,
                ;
                let cost = (columns as u64).saturating_mul(rows as u64);
                self.live = self.live.saturating_sub(cost);
                self.table.set(index, None);
                proof {
                    assert(self.masks().table =~= before.table.update(index as int, None));
                    assert(self.masks().images =~= before.images);
                    assert(super::lemmas::entry_bytes(before.table[index as int]) == cost as nat);
                    super::lemmas::lemma_masks_after_sound(before, view_item(*item));
                }
                Some(depth)
            },
            ExecItem::UploadImage { id, image_width: width, image_height: height, .. } => {
                let ghost before = self.masks();
                let index = *id as usize;
                if index >= MAX_IMAGES {
                    return None;
                }
                let slot = match self.images.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(before.images[index as int] == view_image_entry(slot));
                if slot.is_some() {
                    return None;
                }
                if *width == 0 || *height == 0 {
                    return None;
                }
                if *width as usize > MAX_IMAGE_SIDE || *height as usize > MAX_IMAGE_SIDE {
                    return None;
                }
                let ghost size = ImageSize { width: *width as nat, height: *height as nat };
                proof {
                    super::lemmas::lemma_live_image_bytes_update(before.images, index as int, Some(size));
                    assert(size.width * size.height * 4 <= 1_073_741_824) by (nonlinear_arith)
                        requires
                            size.width <= 16384,
                            size.height <= 16384,
                    ;
                }
                // Neither saturates: the cost is at most 2^30 and live at most 2^28.
                let cost = (*width as u64).saturating_mul(*height as u64).saturating_mul(4);
                let total = self.image_live.saturating_add(cost);
                if total > MAX_IMAGE_BYTES as u64 {
                    return None;
                }
                self.images.set(index, Some((*width, *height)));
                self.image_live = total;
                proof {
                    assert(self.masks().images =~= before.images.update(index as int, Some(size)));
                    assert(self.masks().table =~= before.table);
                }
                Some(depth)
            },
            ExecItem::DrawImage { id, x, y, width, height, src_x, src_y, src_width, src_height, .. } => {
                if !(position_is_ok(*x) && position_is_ok(*y) && size_is_ok(*width) && size_is_ok(*height)) {
                    return None;
                }
                let index = *id as usize;
                if index >= MAX_IMAGES {
                    return None;
                }
                let slot = match self.images.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(self.masks().images[index as int] == view_image_entry(slot));
                match slot {
                    // 6.10 "a draw names a live image and a source rectangle inside it".
                    Some((image_width, image_height)) => {
                        // The sums are of two u16s, so they are exact in usize.
                        let right = (*src_x as usize).saturating_add(*src_width as usize);
                        let bottom = (*src_y as usize).saturating_add(*src_height as usize);
                        if right <= image_width as usize && bottom <= image_height as usize {
                            Some(depth)
                        } else {
                            None
                        }
                    },
                    None => None,
                }
            },
            ExecItem::FreeImage { id } => {
                let ghost before = self.masks();
                let index = *id as usize;
                if index >= MAX_IMAGES {
                    return None;
                }
                let slot = match self.images.as_slice().get(index) {
                    Some(slot) => *slot,
                    None => {
                        return None;
                    },
                };
                assert(before.images[index as int] == view_image_entry(slot));
                let (width, height) = match slot {
                    Some(sides) => sides,
                    None => {
                        return None;
                    },
                };
                proof {
                    super::lemmas::lemma_live_image_bytes_update(before.images, index as int, None);
                }
                // The freed image's bytes are part of image_live, so this is exact, and
                // the product does not saturate: both sides are below 2^16.
                assert((width as nat) * (height as nat) * 4 < 0x4_0000_0000) by (nonlinear_arith)
                    requires
                        (width as nat) < 65536,
                        (height as nat) < 65536,
                ;
                let cost = (width as u64).saturating_mul(height as u64).saturating_mul(4);
                self.image_live = self.image_live.saturating_sub(cost);
                self.images.set(index, None);
                proof {
                    assert(self.masks().images =~= before.images.update(index as int, None));
                    assert(self.masks().table =~= before.table);
                    assert(super::lemmas::image_entry_bytes(before.images[index as int]) == cost as nat);
                    super::lemmas::lemma_masks_after_sound(before, view_item(*item));
                }
                Some(depth)
            },
        }
    }

    /// The validator: `true` if the list passes, leaving the masks [`validate`] gives.
    /// On `false` the caller ends the process, so which items applied does not matter.
    pub fn validate(&mut self, items: &[ExecItem]) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            super::contract::validate_ensures(
                old(self).masks(),
                view_items(items@),
                if ok {
                    Some(final(self).masks())
                } else {
                    None
                },
            ),
    {
        let ghost all = view_items(items@);
        if items.len() > MAX_ITEMS {
            return false;
        }
        let mut depth: usize = 0;
        let mut i: usize = 0;
        assert(all.subrange(0, all.len() as int) =~= all);
        while i < items.len()
            invariant
                i <= items.len(),
                items.len() <= MAX_ITEMS,
                all == view_items(items@),
                self.wf(),
                depth <= MAX_CLIP_DEPTH,
                walk(old(self).masks(), 0, all) == walk(
                    self.masks(),
                    depth as nat,
                    all.subrange(i as int, all.len() as int),
                ),
            decreases items.len() - i,
        {
            let ghost before = self.masks();
            let ghost rest = all.subrange(i as int, all.len() as int);
            let item = match items.get(i) {
                Some(item) => item,
                None => {
                    return false;
                },
            };
            assert(rest[0] == view_item(*item));
            let stepped = self.step(item, depth);
            assert(rest.subrange(1, rest.len() as int) =~= all.subrange(i + 1, all.len() as int));
            depth = match stepped {
                Some(d) => d,
                None => {
                    assert(walk(before, depth as nat, rest) is None);
                    return false;
                },
            };
            // i < items.len(), so this does not saturate.
            i = i.saturating_add(1);
        }
        assert(all.subrange(i as int, all.len() as int) =~= Seq::<Item>::empty());
        depth == 0
    }
}

} // verus!
