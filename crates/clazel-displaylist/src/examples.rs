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

} // verus!
