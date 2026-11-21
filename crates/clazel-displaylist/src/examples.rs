//! Concrete lists, evaluated on the spec. Kept apart from [`super::lemmas`] so that a
//! mutant that breaks one of them does not stop Verus before it checks a kill
//! certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Items at the top of the format's table, byte by byte.
pub proof fn lemma_example_items()
    ensures
        decode(seq![3u8]) == Some(seq![Item::PopClip]),
        decode(seq![6u8, 1, 0, 0, 0]) == Some(seq![Item::FreeMask { id: 1 }]),
        decode(seq![6u8, 0x78, 0x56, 0x34, 0x12]) == Some(seq![Item::FreeMask { id: 0x1234_5678 }]),
        decode(Seq::<u8>::empty()) == Some(Seq::<Item>::empty()),
{
    assert(decode(seq![3u8]) == Some(seq![Item::PopClip])) by (compute_only);
    assert(decode(seq![6u8, 1, 0, 0, 0]) == Some(seq![Item::FreeMask { id: 1 }])) by (compute_only);
    assert(decode(seq![6u8, 0x78, 0x56, 0x34, 0x12]) == Some(seq![Item::FreeMask { id: 0x1234_5678 }])) by (compute_only);
    assert(decode(Seq::<u8>::empty()) == Some(Seq::<Item>::empty())) by (compute_only);
}

/// Positions are signed: all ones is -1.
pub proof fn lemma_example_signed()
    ensures
        i32_of(0xFFFF_FFFF) == -1,
        i32_of(0x8000_0000) == i32::MIN,
        i32_of(0x7FFF_FFFF) == i32::MAX,
        bits_of(-1i32) == 0xFFFF_FFFFnat,
{
}

/// An unknown tag, and an item cut short, are not a list.
pub proof fn lemma_reject_bytes()
    ensures
        decode(seq![0u8]) is None,
        decode(seq![7u8]) is None,
        decode(seq![6u8, 1, 0, 0]) is None,
        decode(seq![3u8, 6u8]) is None,
{
    assert(decode(seq![0u8]) is None) by (compute_only);
    assert(decode(seq![7u8]) is None) by (compute_only);
    assert(decode(seq![6u8, 1, 0, 0]) is None) by (compute_only);
    assert(decode(seq![3u8, 6u8]) is None) by (compute_only);
}

/// A clip must be popped, and only a pushed one can be.
pub proof fn lemma_example_clips()
    ensures
        clip_after(0, Item::PopClip) is None,
        clip_after(1, Item::PopClip) == Some(0nat),
        clip_after(MAX_CLIP_DEPTH as nat, Item::PushClip { x: 0, y: 0, width: 0, height: 0 }) is None,
{
}

/// Positions and sizes stop at 2^23.
pub proof fn lemma_example_ranges()
    ensures
        position_ok(8_388_608),
        position_ok(-8_388_608i32),
        !position_ok(8_388_609),
        !position_ok(-8_388_609i32),
        size_ok(8_388_608),
        !size_ok(8_388_609),
{
}

/// An upload with every field different, and coverage to read.
pub open spec fn sample_upload() -> Item {
    Item::UploadMask { id: 1, columns: 2, rows: 3, coverage: seq![1u8, 2, 3, 4, 5, 6] }
}

/// An upload reads back from its bytes, and they are what the format's table says.
pub proof fn lemma_example_upload()
    ensures
        decode_item(encode_item(sample_upload())) == Some((sample_upload(), 15nat)),
        encode_item(sample_upload()) == seq![4u8, 1, 0, 0, 0, 2, 0, 3, 0, 1, 2, 3, 4, 5, 6],
{
    assert(decode_item(encode_item(sample_upload())) == Some((sample_upload(), 15nat))) by (compute_only);
    assert(encode_item(sample_upload()) == seq![4u8, 1, 0, 0, 0, 2, 0, 3, 0, 1, 2, 3, 4, 5, 6]) by (compute_only);
}

/// The limits' values.
pub proof fn lemma_limits()
    ensures
        MAX_LIST_BYTES == 402_653_184usize,
        MAX_IMAGES == 65_536usize,
        MAX_IMAGE_SIDE == 16_384usize,
        MAX_IMAGE_BYTES == 268_435_456usize,
        MAX_ITEMS == 1_048_576usize,
        MAX_CLIP_DEPTH == 256usize,
        MAX_MASKS == 65_536usize,
        MAX_MASK_SIDE == 2048usize,
        MAX_MASK_BYTES == 67_108_864usize,
        MAX_COORD == 8_388_608usize,
        list_length_ok(402_653_184),
        !list_length_ok(402_653_185),
        image_id_ok(65_535),
        !image_id_ok(65_536),
        item_count_ok(1_048_576),
        !item_count_ok(1_048_577),
        id_ok(65_535),
        !id_ok(65_536),
{
}

/// Tables with mask 0 dead and mask 1 live, of 6 bytes, and image 0 dead and image 1
/// live, of 4 × 3 pixels.
pub open spec fn sample() -> Masks {
    Masks {
        table: seq![None, Some(MaskSize { width: 2, height: 3 })],
        images: seq![None, Some(ImageSize { width: 4, height: 3 })],
    }
}

/// Tables whose one live mask, and whose one live image, fill the whole budget.
pub open spec fn full() -> Masks {
    Masks {
        table: seq![None, Some(MaskSize { width: 8192, height: 8192 })],
        images: seq![None, Some(ImageSize { width: 16384, height: 4096 })],
    }
}

/// An upload, with the coverage left out, which the rules do not read.
pub open spec fn upload(id: u32, columns: u16, rows: u16) -> Item {
    Item::UploadMask { id, columns, rows, coverage: Seq::empty() }
}

/// The mask rules, one case each way.
pub proof fn lemma_example_masks()
    ensures
        masks_after(sample(), Item::DrawMask { id: 0, x: 0, y: 0, colour: 0 }) is None,
        masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 0, colour: 0 }) is Some,
        masks_after(sample(), Item::FreeMask { id: 0 }) is None,
        masks_after(sample(), Item::FreeMask { id: 1 })->Some_0.table[1] is None,
        masks_after(sample(), upload(1, 1, 1)) is None,
        masks_after(sample(), upload(0, 0, 1)) is None,
        masks_after(sample(), upload(0, 1, 0)) is None,
        masks_after(sample(), upload(0, 2049, 1)) is None,
        masks_after(sample(), upload(0, 1, 2049)) is None,
        masks_after(sample(), upload(0, 2048, 1)) is Some,
        masks_after(sample(), upload(0, 1, 1))->Some_0.table[0] is Some,
        masks_after(full(), upload(0, 1, 1)) is None,
        live_bytes(seq![Some(MaskSize { width: 3, height: 4 }), None, Some(MaskSize { width: 1, height: 4 })]) == 16,
{
    assert(masks_after(sample(), Item::DrawMask { id: 0, x: 0, y: 0, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 0, colour: 0 }) is Some) by (compute_only);
    assert(masks_after(sample(), Item::FreeMask { id: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FreeMask { id: 1 })->Some_0.table[1] is None) by (compute_only);
    assert(masks_after(sample(), upload(1, 1, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload(0, 0, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload(0, 1, 0)) is None) by (compute_only);
    assert(masks_after(sample(), upload(0, 2049, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload(0, 1, 2049)) is None) by (compute_only);
    assert(masks_after(sample(), upload(0, 2048, 1)) is Some) by (compute_only);
    assert(masks_after(sample(), upload(0, 1, 1))->Some_0.table[0] is Some) by (compute_only);
    assert(masks_after(full(), upload(0, 1, 1)) is None) by (compute_only);
    assert(live_bytes(seq![Some(MaskSize { width: 3, height: 4 }), None, Some(MaskSize { width: 1, height: 4 })]) == 16) by (compute_only);
}

/// The range rules, for every field of every item that has one.
pub proof fn lemma_example_fields()
    ensures
        masks_after(sample(), Item::FillRect { x: 8_388_609, y: 0, width: 0, height: 0, colour: 0 }) is None,
        masks_after(sample(), Item::FillRect { x: 0, y: 8_388_609, width: 0, height: 0, colour: 0 }) is None,
        masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 8_388_609, height: 0, colour: 0 }) is None,
        masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 0, height: 8_388_609, colour: 0 }) is None,
        masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 0, height: 0, colour: 0 }) is Some,
        masks_after(sample(), Item::PushClip { x: 8_388_609, y: 0, width: 0, height: 0 }) is None,
        masks_after(sample(), Item::PushClip { x: 0, y: 8_388_609, width: 0, height: 0 }) is None,
        masks_after(sample(), Item::PushClip { x: 0, y: 0, width: 8_388_609, height: 0 }) is None,
        masks_after(sample(), Item::PushClip { x: 0, y: 0, width: 0, height: 8_388_609 }) is None,
        masks_after(sample(), Item::DrawMask { id: 1, x: 8_388_609, y: 0, colour: 0 }) is None,
        masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 8_388_609, colour: 0 }) is None,
{
    assert(masks_after(sample(), Item::FillRect { x: 8_388_609, y: 0, width: 0, height: 0, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FillRect { x: 0, y: 8_388_609, width: 0, height: 0, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 8_388_609, height: 0, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 0, height: 8_388_609, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FillRect { x: 0, y: 0, width: 0, height: 0, colour: 0 }) is Some) by (compute_only);
    assert(masks_after(sample(), Item::PushClip { x: 8_388_609, y: 0, width: 0, height: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::PushClip { x: 0, y: 8_388_609, width: 0, height: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::PushClip { x: 0, y: 0, width: 8_388_609, height: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::PushClip { x: 0, y: 0, width: 0, height: 8_388_609 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawMask { id: 1, x: 8_388_609, y: 0, colour: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 8_388_609, colour: 0 }) is None) by (compute_only);
}

/// A list's clips must end balanced, and a pushed clip counts.
pub proof fn lemma_example_walk()
    ensures
        walk(sample(), 0, Seq::empty()) is Some,
        walk(sample(), 1, Seq::empty()) is None,
        clip_after(255, Item::PushClip { x: 0, y: 0, width: 0, height: 0 }) == Some(256nat),
        clip_after(3, Item::PopClip) == Some(2nat),
        clip_after(3, Item::FreeMask { id: 0 }) == Some(3nat),
        walk(sample(), 0, seq![upload(0, 1, 1), Item::DrawMask { id: 0, x: 0, y: 0, colour: 0 }]) is Some,
        walk(sample(), 0, seq![Item::PushClip { x: 0, y: 0, width: 0, height: 0 }, Item::PopClip]) is Some,
        decode(seq![3u8, 6u8, 1, 0, 0, 0]) == Some(seq![Item::PopClip, Item::FreeMask { id: 1 }]),
        no_masks().table[0] is None,
        no_masks().images[0] is None,
{
    assert(walk(sample(), 0, Seq::empty()) is Some) by (compute_only);
    assert(walk(sample(), 1, Seq::empty()) is None) by (compute_only);
    assert(walk(sample(), 0, seq![upload(0, 1, 1), Item::DrawMask { id: 0, x: 0, y: 0, colour: 0 }]) is Some) by (compute_only);
    assert(walk(sample(), 0, seq![Item::PushClip { x: 0, y: 0, width: 0, height: 0 }, Item::PopClip]) is Some) by (compute_only);
    assert(decode(seq![3u8, 6u8, 1, 0, 0, 0]) == Some(seq![Item::PopClip, Item::FreeMask { id: 1 }])) by (compute_only);
}

/// An image upload with every field different, and pixels to read.
pub open spec fn sample_image() -> Item {
    Item::UploadImage { id: 1, image_width: 2, image_height: 1, pixels: seq![1u8, 2, 3, 4, 5, 6, 7, 8] }
}

/// An image draw with every field different, linear.
pub open spec fn sample_draw() -> Item {
    Item::DrawImage {
        id: 1,
        x: -1i32,
        y: 2,
        width: 3,
        height: 4,
        src_x: 5,
        src_y: 6,
        src_width: 7,
        src_height: 8,
        linear: true,
    }
}

/// An image upload reads back from its bytes, and they are what the format's table says.
pub proof fn lemma_example_image_upload()
    ensures
        encode_item(sample_image()) == seq![7u8, 1, 0, 0, 0, 2, 0, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8],
        decode_item(encode_item(sample_image())) == Some((sample_image(), 17nat)),
{
    assert(encode_item(sample_image()) == seq![7u8, 1, 0, 0, 0, 2, 0, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8]) by (compute_only);
    assert(decode_item(encode_item(sample_image())) == Some((sample_image(), 17nat))) by (compute_only);
}

/// The bytes of an image draw, byte by byte.
pub open spec fn sample_draw_bytes() -> Seq<u8> {
    seq![8u8, 1, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 6, 0, 7, 0, 8, 0, 1]
}

/// An image draw writes as the format's table says.
pub proof fn lemma_example_image_draw_bytes()
    ensures
        encode_item(sample_draw()) == sample_draw_bytes(),
{
    assert(encode_item(sample_draw()) == sample_draw_bytes()) by (compute_only);
}

/// An image draw reads back from those bytes.
pub proof fn lemma_example_image_draw_reads()
    ensures
        decode_item(sample_draw_bytes()) == Some((sample_draw(), 30nat)),
{
    assert(decode_item(sample_draw_bytes()) == Some((sample_draw(), 30nat))) by (compute_only);
}

/// A freed image reads, and what is cut short or unknown does not.
pub proof fn lemma_example_image_free_and_rejects()
    ensures
        decode(seq![9u8, 1, 0, 0, 0]) == Some(seq![Item::FreeImage { id: 1 }]),
        decode(seq![9u8, 0x78, 0x56, 0x34, 0x12]) == Some(seq![Item::FreeImage { id: 0x1234_5678 }]),
        decode(seq![9u8, 1, 0, 0]) is None,
        decode(seq![10u8]) is None,
        decode(seq![7u8, 1, 0, 0, 0, 1, 0, 1, 0, 1, 2, 3]) is None,
{
    assert(decode(seq![9u8, 1, 0, 0, 0]) == Some(seq![Item::FreeImage { id: 1 }])) by (compute_only);
    assert(decode(seq![9u8, 0x78, 0x56, 0x34, 0x12]) == Some(seq![Item::FreeImage { id: 0x1234_5678 }])) by (compute_only);
    assert(decode(seq![9u8, 1, 0, 0]) is None) by (compute_only);
    assert(decode(seq![10u8]) is None) by (compute_only);
    assert(decode(seq![7u8, 1, 0, 0, 0, 1, 0, 1, 0, 1, 2, 3]) is None) by (compute_only);
}

/// An image draw whose filter byte is 2 is not an item, and one whose is 0 is.
pub proof fn lemma_example_image_filter_byte()
    ensures
        decode_item(sample_draw_bytes().update(29, 2u8)) is None,
        decode_item(sample_draw_bytes().update(29, 0u8)) is Some,
        decode_item(sample_draw_bytes().update(29, 0u8))->Some_0.0 is DrawImage,
        decode_item(sample_draw_bytes().update(29, 0u8))->Some_0.0->DrawImage_linear == false,
{
    assert(decode_item(sample_draw_bytes().update(29, 2u8)) is None) by (compute_only);
    assert(decode_item(sample_draw_bytes().update(29, 0u8)) is Some) by (compute_only);
    assert(decode_item(sample_draw_bytes().update(29, 0u8))->Some_0.0 is DrawImage) by (compute_only);
    assert(decode_item(sample_draw_bytes().update(29, 0u8))->Some_0.0->DrawImage_linear == false) by (compute_only);
}

/// An image upload, with the pixels left out, which the rules do not read.
pub open spec fn upload_image(id: u32, width: u16, height: u16) -> Item {
    Item::UploadImage { id, image_width: width, image_height: height, pixels: Seq::empty() }
}

/// An image draw of a source rectangle, at the origin.
pub open spec fn draw_image(id: u32, src_x: u16, src_y: u16, src_width: u16, src_height: u16) -> Item {
    Item::DrawImage {
        id,
        x: 0,
        y: 0,
        width: 1,
        height: 1,
        src_x,
        src_y,
        src_width,
        src_height,
        linear: false,
    }
}

/// The image rules, one case each way. Image 1 is 4 × 3 in `sample()`.
pub proof fn lemma_example_images()
    ensures
        masks_after(sample(), upload_image(1, 1, 1)) is None,
        masks_after(sample(), upload_image(0, 0, 1)) is None,
        masks_after(sample(), upload_image(0, 1, 0)) is None,
        masks_after(sample(), upload_image(0, 16385, 1)) is None,
        masks_after(sample(), upload_image(0, 1, 16385)) is None,
        masks_after(sample(), upload_image(0, 16384, 1)) is Some,
        masks_after(sample(), upload_image(0, 1, 1))->Some_0.images[0] is Some,
        masks_after(sample(), upload_image(0, 1, 1))->Some_0.table == sample().table,
        masks_after(sample(), upload_image(0, 7, 5))->Some_0.images[0] == Some(ImageSize { width: 7, height: 5 }),
        masks_after(full(), upload_image(0, 1, 1)) is None,
        masks_after(sample(), Item::FreeImage { id: 0 }) is None,
        masks_after(sample(), Item::FreeImage { id: 1 })->Some_0.images[1] is None,
        masks_after(sample(), Item::FreeImage { id: 1 })->Some_0.table == sample().table,
        masks_after(sample(), draw_image(0, 0, 0, 0, 0)) is None,
        masks_after(sample(), draw_image(1, 0, 0, 4, 3)) is Some,
        masks_after(sample(), draw_image(1, 1, 0, 4, 3)) is None,
        masks_after(sample(), draw_image(1, 0, 1, 4, 3)) is None,
        masks_after(sample(), draw_image(1, 0, 0, 5, 3)) is None,
        masks_after(sample(), draw_image(1, 0, 0, 4, 4)) is None,
        masks_after(sample(), draw_image(1, 3, 2, 1, 1)) is Some,
        masks_after(sample(), draw_image(1, 4, 3, 0, 0)) is Some,
        masks_after(sample(), draw_image(1, 4, 3, 1, 0)) is None,
        masks_after(sample(), draw_image(1, 65535, 65535, 65535, 65535)) is None,
        masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 0, colour: 0 }) is Some,
        masks_after(sample(), Item::FreeMask { id: 0 }) is None,
        live_image_bytes(seq![Some(ImageSize { width: 3, height: 4 }), None, Some(ImageSize { width: 1, height: 4 })]) == 64,
{
    assert(masks_after(sample(), upload_image(1, 1, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 0, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 1, 0)) is None) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 16385, 1)) is None) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 1, 16385)) is None) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 16384, 1)) is Some) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 1, 1))->Some_0.images[0] is Some) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 1, 1))->Some_0.table == sample().table) by (compute_only);
    assert(masks_after(sample(), upload_image(0, 7, 5))->Some_0.images[0] == Some(ImageSize { width: 7, height: 5 }))
        by (compute_only);
    assert(masks_after(full(), upload_image(0, 1, 1)) is None) by (compute_only);
    assert(masks_after(sample(), Item::FreeImage { id: 0 }) is None) by (compute_only);
    assert(masks_after(sample(), Item::FreeImage { id: 1 })->Some_0.images[1] is None) by (compute_only);
    assert(masks_after(sample(), Item::FreeImage { id: 1 })->Some_0.table == sample().table) by (compute_only);
    assert(masks_after(sample(), draw_image(0, 0, 0, 0, 0)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 0, 0, 4, 3)) is Some) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 1, 0, 4, 3)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 0, 1, 4, 3)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 0, 0, 5, 3)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 0, 0, 4, 4)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 3, 2, 1, 1)) is Some) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 4, 3, 0, 0)) is Some) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 4, 3, 1, 0)) is None) by (compute_only);
    assert(masks_after(sample(), draw_image(1, 65535, 65535, 65535, 65535)) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawMask { id: 1, x: 0, y: 0, colour: 0 }) is Some) by (compute_only);
    assert(masks_after(sample(), Item::FreeMask { id: 0 }) is None) by (compute_only);
    assert(live_image_bytes(seq![Some(ImageSize { width: 3, height: 4 }), None, Some(ImageSize { width: 1, height: 4 })]) == 64)
        by (compute_only);
}

/// The destination of an image draw has tag 1's range rules.
pub proof fn lemma_example_image_fields()
    ensures
        masks_after(sample(), Item::DrawImage {
            id: 1, x: 8_388_609, y: 0, width: 0, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
        }) is None,
        masks_after(sample(), Item::DrawImage {
            id: 1, x: 0, y: 8_388_609, width: 0, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
        }) is None,
        masks_after(sample(), Item::DrawImage {
            id: 1, x: 0, y: 0, width: 8_388_609, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
        }) is None,
        masks_after(sample(), Item::DrawImage {
            id: 1, x: 0, y: 0, width: 0, height: 8_388_609, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
        }) is None,
        masks_after(sample(), Item::DrawImage {
            id: 1, x: -8_388_608i32, y: 8_388_608, width: 8_388_608, height: 8_388_608, src_x: 0, src_y: 0,
            src_width: 4, src_height: 3, linear: true,
        }) is Some,
{
    assert(masks_after(sample(), Item::DrawImage {
        id: 1, x: 8_388_609, y: 0, width: 0, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
    }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawImage {
        id: 1, x: 0, y: 8_388_609, width: 0, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
    }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawImage {
        id: 1, x: 0, y: 0, width: 8_388_609, height: 0, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
    }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawImage {
        id: 1, x: 0, y: 0, width: 0, height: 8_388_609, src_x: 0, src_y: 0, src_width: 0, src_height: 0, linear: false,
    }) is None) by (compute_only);
    assert(masks_after(sample(), Item::DrawImage {
        id: 1, x: -8_388_608i32, y: 8_388_608, width: 8_388_608, height: 8_388_608, src_x: 0, src_y: 0,
        src_width: 4, src_height: 3, linear: true,
    }) is Some) by (compute_only);
}

} // verus!
