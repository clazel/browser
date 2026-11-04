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
        MAX_LIST_BYTES == 134_217_728usize,
        MAX_ITEMS == 1_048_576usize,
        MAX_CLIP_DEPTH == 256usize,
        MAX_MASKS == 65_536usize,
        MAX_MASK_SIDE == 2048usize,
        MAX_MASK_BYTES == 67_108_864usize,
        MAX_COORD == 8_388_608usize,
        list_length_ok(134_217_728),
        !list_length_ok(134_217_729),
        item_count_ok(1_048_576),
        !item_count_ok(1_048_577),
        id_ok(65_535),
        !id_ok(65_536),
{
}

/// A table with mask 0 dead and mask 1 live, of 6 bytes.
pub open spec fn sample() -> Masks {
    Masks { table: seq![None, Some(MaskSize { width: 2, height: 3 })] }
}

/// A table whose one live mask fills the whole budget.
pub open spec fn full() -> Masks {
    Masks { table: seq![None, Some(MaskSize { width: 8192, height: 8192 })] }
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
{
    assert(walk(sample(), 0, Seq::empty()) is Some) by (compute_only);
    assert(walk(sample(), 1, Seq::empty()) is None) by (compute_only);
    assert(walk(sample(), 0, seq![upload(0, 1, 1), Item::DrawMask { id: 0, x: 0, y: 0, colour: 0 }]) is Some) by (compute_only);
    assert(walk(sample(), 0, seq![Item::PushClip { x: 0, y: 0, width: 0, height: 0 }, Item::PopClip]) is Some) by (compute_only);
    assert(decode(seq![3u8, 6u8, 1, 0, 0, 0]) == Some(seq![Item::PopClip, Item::FreeMask { id: 1 }])) by (compute_only);
}

} // verus!
