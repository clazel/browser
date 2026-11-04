//! What the executable code is proven to satisfy, and the theorems proven about the
//! spec (phase-5.md item 5.17a). `lemmas.rs` holds the proofs.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------- the code

/// Every item of a list can be written.
pub open spec fn all_encodable(items: Seq<Item>) -> bool {
    forall|i: int| 0 <= i < items.len() ==> encodable(#[trigger] items[i])
}

/// Contract for the encoder: `None` exactly when an item cannot be written.
pub open spec fn encode_ensures(items: Seq<Item>, output: Option<Seq<u8>>) -> bool {
    output == if all_encodable(items) {
        Some(encode(items))
    } else {
        None
    }
}

/// Contract for the decoder.
pub open spec fn decode_ensures(bytes: Seq<u8>, output: Option<Seq<Item>>) -> bool {
    output == decode(bytes)
}

/// Contract for the validator, which keeps the masks between lists: on success it
/// holds what [`validate`] gives, and on refusal the caller ends the process, so what
/// it holds then does not matter.
pub open spec fn validate_ensures(before: Masks, items: Seq<Item>, output: Option<Masks>) -> bool {
    output == validate(before, items)
}

// ---------------------------------------------------------------- the theorems

/// `theorem_decode_encode_roundtrip`: a list that can be written reads back the same.
pub open spec fn decode_inverts_encode() -> bool {
    forall|items: Seq<Item>|
        all_encodable(items) && encode(items).len() <= (MAX_LIST_BYTES as nat)
            ==> decode(#[trigger] encode(items)) == Some(items)
}

/// `theorem_encode_decode_roundtrip`: bytes have one reading, so a list has one
/// encoding, and nothing can hide in the bytes of a list that decodes.
pub open spec fn encode_inverts_decode() -> bool {
    forall|bytes: Seq<u8>|
        (#[trigger] decode(bytes)) is Some ==> encode(decode(bytes)->Some_0) == bytes
}

/// `theorem_decode_bounded`: a list's items number at most its bytes, so decoding
/// is linear, and each can be written.
pub open spec fn decode_is_bounded() -> bool {
    forall|bytes: Seq<u8>|
        (#[trigger] decode(bytes)) is Some ==> {
            &&& decode(bytes)->Some_0.len() <= bytes.len()
            &&& all_encodable(decode(bytes)->Some_0)
        }
}

/// What a list that passes means to `clazel-gpu`: at most [`MAX_ITEMS`] items, every
/// number in every item in range, every clip popped and never deeper than
/// [`MAX_CLIP_DEPTH`] or below empty, and a table within the budget left behind.
pub open spec fn list_is_sound(items: Seq<Item>, after: Masks) -> bool {
    &&& items.len() <= (MAX_ITEMS as nat)
    &&& masks_ok(after)
    &&& forall|i: int| 0 <= i < items.len() ==> in_range(#[trigger] items[i])
    &&& depth_at(items, items.len()) == 0
    &&& forall|n: nat| n <= items.len() ==> 0 <= #[trigger] depth_at(items, n) <= (MAX_CLIP_DEPTH as nat)
}

/// `theorem_validated_bounds`: every list that passes is sound.
pub open spec fn validated_bounds() -> bool {
    forall|before: Masks, items: Seq<Item>|
        masks_ok(before) && (#[trigger] validate(before, items)) is Some
            ==> list_is_sound(items, validate(before, items)->Some_0)
}

/// The masks a list has made by item `n`, if it has broken no rule by then.
pub open spec fn masks_at(before: Masks, items: Seq<Item>, n: nat) -> Masks
    decreases n,
{
    if n == 0 || n > items.len() {
        before
    } else {
        let earlier = masks_at(before, items, (n - 1) as nat);
        match masks_after(earlier, items[n - 1]) {
            Some(masks) => masks,
            None => earlier,
        }
    }
}

/// `theorem_draws_are_live`: a mask is drawn only while it lives. Every `DrawMask` in
/// a list that passes names a mask live at that point: the found table with the
/// list's earlier uploads and frees applied.
pub open spec fn draws_are_live() -> bool {
    forall|before: Masks, items: Seq<Item>, i: int|
        #![trigger validate(before, items), items[i]]
        masks_ok(before)
            && validate(before, items) is Some
            && 0 <= i < items.len()
            && items[i] is DrawMask
            ==> is_live(masks_at(before, items, i as nat), items[i]->DrawMask_id)
}

/// `theorem_no_masks_ok`: a process starts with no masks, which satisfy the invariant.
pub open spec fn no_masks_are_ok() -> bool {
    masks_ok(no_masks())
}

} // verus!
