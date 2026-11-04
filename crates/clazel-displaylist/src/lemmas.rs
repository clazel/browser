//! Facts proven about the spec, and the theorems `contract.rs` states.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------- numbers

/// `256^n`.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// The powers these formats use.
pub proof fn lemma_pow256_values()
    ensures
        pow256(0) == 1,
        pow256(1) == 256,
        pow256(2) == 65536,
        pow256(3) == 16777216,
        pow256(4) == 0x1_0000_0000nat,
{
    reveal_with_fuel(pow256, 5);
}

/// `le_bytes` gives as many bytes as asked for.
pub proof fn lemma_le_bytes_len(n: nat, width: nat)
    ensures
        le_bytes(n, width).len() == width,
    decreases width,
{
    if width > 0 {
        lemma_le_bytes_len(n / 256, (width - 1) as nat);
    }
}

/// A number fits in as many bytes as hold it.
pub proof fn lemma_le_value_bound(s: Seq<u8>)
    ensures
        le_value(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.subrange(1, s.len() as int);
        lemma_le_value_bound(rest);
        assert(pow256(s.len()) == 256 * pow256(rest.len()));
        assert(s[0] as nat <= 255);
        assert(le_value(s) == s[0] as nat + 256 * le_value(rest));
        assert(le_value(rest) + 1 <= pow256(rest.len()));
        assert(256 * (le_value(rest) + 1) <= 256 * pow256(rest.len())) by (nonlinear_arith)
            requires
                le_value(rest) + 1 <= pow256(rest.len()),
        ;
    }
}

/// Reading what was written gives the number back.
pub proof fn lemma_le_value_of_bytes(n: nat, width: nat)
    requires
        n < pow256(width),
    ensures
        le_value(le_bytes(n, width)) == n,
    decreases width,
{
    if width > 0 {
        let w = (width - 1) as nat;
        assert(n / 256 < pow256(w)) by {
            assert(pow256(width) == 256 * pow256(w));
            vstd::arithmetic::div_mod::lemma_div_is_ordered(n as int, pow256(width) as int - 1, 256);
            assert((256 * pow256(w) - 1) / 256 < pow256(w)) by (nonlinear_arith)
                requires
                    pow256(w) >= 1,
            {
            }
        }
        lemma_pow256_positive(w);
        lemma_le_value_of_bytes(n / 256, w);
        lemma_le_bytes_len(n / 256, w);
        let whole = le_bytes(n, width);
        assert(whole.subrange(1, whole.len() as int) =~= le_bytes(n / 256, w));
        assert(whole[0] as nat == n % 256);
        assert(n == 256 * (n / 256) + n % 256) by (nonlinear_arith);
    }
}

/// `256^n` is positive.
pub proof fn lemma_pow256_positive(n: nat)
    ensures
        pow256(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow256_positive((n - 1) as nat);
    }
}

/// Writing what was read gives the bytes back.
pub proof fn lemma_le_bytes_of_value(s: Seq<u8>)
    ensures
        le_bytes(le_value(s), s.len()) =~= s,
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.subrange(1, s.len() as int);
        lemma_le_bytes_of_value(rest);
        let v = le_value(s);
        assert(v == s[0] as nat + 256 * le_value(rest));
        assert(v / 256 == le_value(rest) && v % 256 == s[0] as nat) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                v as int,
                256,
                le_value(rest) as int,
                s[0] as int,
            );
        }
        assert((v % 256) as u8 == s[0]);
    }
}

/// A signed number's bits read back as the number.
pub proof fn lemma_i32_of_bits(v: i32)
    ensures
        bits_of(v) < 0x1_0000_0000nat,
        i32_of(bits_of(v)) == v,
{
}

/// A 32-bit number reads as a signed number whose bits are that number.
pub proof fn lemma_bits_of_i32(n: nat)
    requires
        n < 0x1_0000_0000nat,
    ensures
        bits_of(i32_of(n)) == n,
{
}

// ---------------------------------------------------------------- fields

/// A four-byte field of `s` holds `n` when its bytes are those of `n`.
proof fn lemma_field4_is(s: Seq<u8>, at: int, n: nat)
    requires
        0 <= at,
        at + 4 <= s.len(),
        s.subrange(at, at + 4) =~= le_bytes(n, 4),
        n < 0x1_0000_0000nat,
    ensures
        field4(s, at) == n,
{
    lemma_pow256_values();
    lemma_le_value_of_bytes(n, 4);
}

/// A two-byte field of `s` holds `n` when its bytes are those of `n`.
proof fn lemma_field2_is(s: Seq<u8>, at: int, n: nat)
    requires
        0 <= at,
        at + 2 <= s.len(),
        s.subrange(at, at + 2) =~= le_bytes(n, 2),
        n < 65536,
    ensures
        field2(s, at) == n,
{
    lemma_pow256_values();
    lemma_le_value_of_bytes(n, 2);
}

/// The length of an item's bytes.
pub proof fn lemma_encode_item_len(item: Item)
    ensures
        encode_item(item).len() == match item {
            Item::FillRect { .. } => 21,
            Item::PushClip { .. } => 17,
            Item::PopClip => 1,
            Item::UploadMask { coverage, .. } => 9 + coverage.len(),
            Item::DrawMask { .. } => 17,
            Item::FreeMask { .. } => 5,
        },
        encode_item(item).len() >= 1,
{
    match item {
        Item::FillRect { x, y, width, height, colour } => {
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(width as nat, 4);
            lemma_le_bytes_len(height as nat, 4);
            lemma_le_bytes_len(colour as nat, 4);
        },
        Item::PushClip { x, y, width, height } => {
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(width as nat, 4);
            lemma_le_bytes_len(height as nat, 4);
        },
        Item::PopClip => {},
        Item::UploadMask { id, columns, rows, coverage } => {
            lemma_le_bytes_len(id as nat, 4);
            lemma_le_bytes_len(columns as nat, 2);
            lemma_le_bytes_len(rows as nat, 2);
        },
        Item::DrawMask { id, x, y, colour } => {
            lemma_le_bytes_len(id as nat, 4);
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(colour as nat, 4);
        },
        Item::FreeMask { id } => {
            lemma_le_bytes_len(id as nat, 4);
        },
    }
}

/// An item that can be written reads back from the start of any bytes beginning with
/// it.
pub proof fn lemma_decode_item_encode(item: Item, rest: Seq<u8>)
    requires
        encodable(item),
    ensures
        decode_item(encode_item(item) + rest) == Some((item, encode_item(item).len())),
{
    lemma_encode_item_len(item);
    lemma_pow256_values();
    let s = encode_item(item) + rest;
    match item {
        Item::FillRect { x, y, width, height, colour } => {
            lemma_i32_of_bits(x);
            lemma_i32_of_bits(y);
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(width as nat, 4);
            lemma_le_bytes_len(height as nat, 4);
            lemma_le_bytes_len(colour as nat, 4);
            assert(s[0] == 1u8);
            lemma_field4_is(s, 1, bits_of(x));
            lemma_field4_is(s, 5, bits_of(y));
            lemma_field4_is(s, 9, width as nat);
            lemma_field4_is(s, 13, height as nat);
            lemma_field4_is(s, 17, colour as nat);
        },
        Item::PushClip { x, y, width, height } => {
            lemma_i32_of_bits(x);
            lemma_i32_of_bits(y);
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(width as nat, 4);
            lemma_le_bytes_len(height as nat, 4);
            assert(s[0] == 2u8);
            lemma_field4_is(s, 1, bits_of(x));
            lemma_field4_is(s, 5, bits_of(y));
            lemma_field4_is(s, 9, width as nat);
            lemma_field4_is(s, 13, height as nat);
        },
        Item::PopClip => {
            assert(s[0] == 3u8);
        },
        Item::UploadMask { id, columns, rows, coverage } => {
            lemma_le_bytes_len(id as nat, 4);
            lemma_le_bytes_len(columns as nat, 2);
            lemma_le_bytes_len(rows as nat, 2);
            assert(s[0] == 4u8);
            lemma_field4_is(s, 1, id as nat);
            lemma_field2_is(s, 5, columns as nat);
            lemma_field2_is(s, 7, rows as nat);
            assert(s.subrange(9, 9 + coverage.len() as int) =~= coverage);
        },
        Item::DrawMask { id, x, y, colour } => {
            lemma_i32_of_bits(x);
            lemma_i32_of_bits(y);
            lemma_le_bytes_len(id as nat, 4);
            lemma_le_bytes_len(bits_of(x), 4);
            lemma_le_bytes_len(bits_of(y), 4);
            lemma_le_bytes_len(colour as nat, 4);
            assert(s[0] == 5u8);
            lemma_field4_is(s, 1, id as nat);
            lemma_field4_is(s, 5, bits_of(x));
            lemma_field4_is(s, 9, bits_of(y));
            lemma_field4_is(s, 13, colour as nat);
        },
        Item::FreeMask { id } => {
            lemma_le_bytes_len(id as nat, 4);
            assert(s[0] == 6u8);
            lemma_field4_is(s, 1, id as nat);
        },
    }
}

// ---------------------------------------------------------------- lists

/// `theorem_decode_encode_roundtrip`, without the length limit.
pub proof fn lemma_decode_items_encode(items: Seq<Item>)
    requires
        super::contract::all_encodable(items),
    ensures
        decode_items(encode(items)) == Some(items),
    decreases items.len(),
{
    if items.len() == 0 {
        assert(encode(items) =~= Seq::<u8>::empty());
    } else {
        let tail = items.subrange(1, items.len() as int);
        assert(encodable(items[0]));
        assert(super::contract::all_encodable(tail)) by {
            assert forall|i: int| 0 <= i < tail.len() implies encodable(#[trigger] tail[i]) by {
                assert(tail[i] == items[i + 1]);
                assert(encodable(items[i + 1]));
            }
        }
        lemma_decode_items_encode(tail);
        let first = encode_item(items[0]);
        let rest = encode(tail);
        let s = encode(items);
        assert(s == first + rest);
        lemma_decode_item_encode(items[0], rest);
        lemma_encode_item_len(items[0]);
        assert(s.subrange(first.len() as int, s.len() as int) =~= rest);
        assert(seq![items[0]] + tail =~= items);
    }
}

/// `theorem_decode_encode_roundtrip`.
pub proof fn theorem_decode_encode_roundtrip()
    ensures
        super::contract::decode_inverts_encode(),
{
    assert forall|items: Seq<Item>|
        super::contract::all_encodable(items) && encode(items).len() <= (MAX_LIST_BYTES as nat)
            implies decode(#[trigger] encode(items)) == Some(items) by {
        lemma_decode_items_encode(items);
    }
}

/// An item read from the start of `s` takes some of `s`, can be written, and its bytes
/// are exactly those it took.
pub proof fn lemma_decode_item_sound(s: Seq<u8>)
    requires
        decode_item(s) is Some,
    ensures
        ({
            let (item, taken) = decode_item(s)->Some_0;
            &&& 0 < taken <= s.len()
            &&& encodable(item)
            &&& encode_item(item) =~= s.subrange(0, taken as int)
        }),
{
    lemma_pow256_values();
    let (item, taken) = decode_item(s)->Some_0;
    if s[0] == 1u8 || s[0] == 2u8 || s[0] == 5u8 || s[0] == 6u8 {
        // Every four-byte field round-trips, as a signed or unsigned number.
        assert forall|a: int| 0 <= a && a + 4 <= s.len() implies {
            &&& #[trigger] field4(s, a) < 0x1_0000_0000nat
            &&& le_bytes(field4(s, a), 4) =~= s.subrange(a, a + 4)
            &&& le_bytes(bits_of(i32_of(field4(s, a))), 4) =~= s.subrange(a, a + 4)
            &&& (field4(s, a) as u32) as nat == field4(s, a)
        } by {
            lemma_le_value_bound(s.subrange(a, a + 4));
            lemma_le_bytes_of_value(s.subrange(a, a + 4));
            lemma_bits_of_i32(field4(s, a));
        }
    }
    if s[0] == 1u8 {
        lemma_encode_item_len(item);
        assert(encode_item(item) =~= s.subrange(0, 21));
    } else if s[0] == 2u8 {
        lemma_encode_item_len(item);
        assert(encode_item(item) =~= s.subrange(0, 17));
    } else if s[0] == 3u8 {
        assert(encode_item(item) =~= s.subrange(0, 1));
    } else if s[0] == 4u8 {
        let a = s.subrange(1, 5);
        let b = s.subrange(5, 7);
        let c = s.subrange(7, 9);
        lemma_le_value_bound(a);
        lemma_le_value_bound(b);
        lemma_le_value_bound(c);
        lemma_le_bytes_of_value(a);
        lemma_le_bytes_of_value(b);
        lemma_le_bytes_of_value(c);
        lemma_encode_item_len(item);
        assert(encode_item(item) =~= s.subrange(0, taken as int));
    } else if s[0] == 5u8 {
        lemma_encode_item_len(item);
        assert(encode_item(item) =~= s.subrange(0, 17));
    } else if s[0] == 6u8 {
        lemma_encode_item_len(item);
        assert(encode_item(item) =~= s.subrange(0, 5));
    }
}

/// The items read from `s` number at most its bytes, each can be written, and writing
/// them gives `s`.
pub proof fn lemma_decode_items_sound(s: Seq<u8>)
    requires
        decode_items(s) is Some,
    ensures
        ({
            let items = decode_items(s)->Some_0;
            &&& items.len() <= s.len()
            &&& super::contract::all_encodable(items)
            &&& encode(items) =~= s
        }),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(encode(Seq::<Item>::empty()) =~= Seq::<u8>::empty());
    } else {
        lemma_decode_item_sound(s);
        let (item, taken) = decode_item(s)->Some_0;
        let suffix = s.subrange(taken as int, s.len() as int);
        lemma_decode_items_sound(suffix);
        let rest = decode_items(suffix)->Some_0;
        let items = seq![item] + rest;
        assert(decode_items(s)->Some_0 == items);
        assert(items.subrange(1, items.len() as int) =~= rest);
        assert(items[0] == item);
        assert(encode(items) == encode_item(item) + encode(rest));
        assert(encode(items) =~= s.subrange(0, taken as int) + suffix);
        assert(s.subrange(0, taken as int) + suffix =~= s);
        assert forall|i: int| 0 <= i < items.len() implies encodable(#[trigger] items[i]) by {
            if i > 0 {
                assert(items[i] == rest[i - 1]);
                assert(encodable(rest[i - 1]));
            }
        }
    }
}

/// `theorem_encode_decode_roundtrip`.
pub proof fn theorem_encode_decode_roundtrip()
    ensures
        super::contract::encode_inverts_decode(),
{
    assert forall|bytes: Seq<u8>| (#[trigger] decode(bytes)) is Some implies encode(
        decode(bytes)->Some_0,
    ) == bytes by {
        lemma_decode_items_sound(bytes);
    }
}

/// `theorem_decode_bounded`.
pub proof fn theorem_decode_bounded()
    ensures
        super::contract::decode_is_bounded(),
{
    assert forall|bytes: Seq<u8>| (#[trigger] decode(bytes)) is Some implies {
        &&& decode(bytes)->Some_0.len() <= bytes.len()
        &&& super::contract::all_encodable(decode(bytes)->Some_0)
    } by {
        lemma_decode_items_sound(bytes);
    }
}

// ---------------------------------------------------------------- masks

/// What one table entry costs.
pub open spec fn entry_bytes(entry: Option<MaskSize>) -> nat {
    match entry {
        None => 0,
        Some(size) => size.width * size.height,
    }
}

/// Changing one entry changes the total by that entry's cost.
pub proof fn lemma_live_bytes_update(table: Seq<Option<MaskSize>>, i: int, entry: Option<MaskSize>)
    requires
        0 <= i < table.len(),
    ensures
        live_bytes(table.update(i, entry)) + entry_bytes(table[i]) == live_bytes(table) + entry_bytes(entry),
    decreases table.len(),
{
    let updated = table.update(i, entry);
    let tail = table.subrange(1, table.len() as int);
    if i == 0 {
        assert(updated.subrange(1, updated.len() as int) =~= tail);
    } else {
        assert(updated.subrange(1, updated.len() as int) =~= tail.update(i - 1, entry));
        lemma_live_bytes_update(tail, i - 1, entry);
        assert(tail[i - 1] == table[i]);
    }
}

/// A table with no live mask costs nothing.
pub proof fn lemma_live_bytes_none(table: Seq<Option<MaskSize>>)
    requires
        forall|i: int| 0 <= i < table.len() ==> table[i] is None,
    ensures
        live_bytes(table) == 0,
    decreases table.len(),
{
    if table.len() > 0 {
        let tail = table.subrange(1, table.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies tail[i] is None by {
            assert(tail[i] == table[i + 1]);
        }
        lemma_live_bytes_none(tail);
    }
}

/// `theorem_no_masks_ok`.
pub proof fn theorem_no_masks_ok()
    ensures
        super::contract::no_masks_are_ok(),
{
    lemma_live_bytes_none(no_masks().table);
}

/// One item keeps a table sound and is in range.
pub proof fn lemma_masks_after_sound(masks: Masks, item: Item)
    requires
        masks_ok(masks),
        masks_after(masks, item) is Some,
    ensures
        masks_ok(masks_after(masks, item)->Some_0),
        in_range(item),
{
    match item {
        Item::FreeMask { id } => {
            let i = id as int;
            lemma_live_bytes_update(masks.table, i, None);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------- clips

/// What one item does to the clip stack's depth.
pub open spec fn clip_delta(item: Item) -> int {
    match item {
        Item::PushClip { .. } => 1int,
        Item::PopClip => -1int,
        _ => 0int,
    }
}

/// Dropping the first item moves [`depth_at`] by that item's change.
pub proof fn lemma_depth_at_tail(items: Seq<Item>, n: nat)
    requires
        items.len() > 0,
        n < items.len(),
    ensures
        depth_at(items, n + 1) == clip_delta(items[0]) + depth_at(items.subrange(1, items.len() as int), n),
    decreases n,
{
    let tail = items.subrange(1, items.len() as int);
    if n > 0 {
        lemma_depth_at_tail(items, (n - 1) as nat);
        assert(items[n as int] == tail[n - 1]);
    }
    assert(depth_at(items, 0) == 0);
    assert(depth_at(tail, 0) == 0);
}

/// A walk that succeeds is sound from where it began.
pub proof fn lemma_walk_sound(masks: Masks, depth: nat, items: Seq<Item>)
    requires
        masks_ok(masks),
        depth <= (MAX_CLIP_DEPTH as nat),
        walk(masks, depth, items) is Some,
    ensures
        masks_ok(walk(masks, depth, items)->Some_0),
        forall|i: int| 0 <= i < items.len() ==> in_range(#[trigger] items[i]),
        depth + depth_at(items, items.len()) == 0,
        forall|n: nat| n <= items.len() ==> 0 <= depth + #[trigger] depth_at(items, n) <= (MAX_CLIP_DEPTH as nat),
    decreases items.len(),
{
    if items.len() == 0 {
        assert(depth_at(items, 0) == 0);
    } else {
        let tail = items.subrange(1, items.len() as int);
        let next = masks_after(masks, items[0])->Some_0;
        let next_depth = clip_after(depth, items[0])->Some_0;
        lemma_masks_after_sound(masks, items[0]);
        assert(next_depth as int == depth + clip_delta(items[0]));
        assert(next_depth <= (MAX_CLIP_DEPTH as nat));
        lemma_walk_sound(next, next_depth, tail);
        assert forall|i: int| 0 <= i < items.len() implies in_range(#[trigger] items[i]) by {
            if i > 0 {
                assert(items[i] == tail[i - 1]);
                assert(in_range(tail[i - 1]));
            }
        }
        lemma_depth_at_tail(items, (items.len() - 1) as nat);
        assert(depth_at(tail, tail.len()) + next_depth == 0);
        assert forall|n: nat| n <= items.len() implies 0 <= depth + #[trigger] depth_at(items, n) <= (MAX_CLIP_DEPTH as nat) by {
            if n > 0 {
                let m = (n - 1) as nat;
                lemma_depth_at_tail(items, m);
                assert(0 <= next_depth + depth_at(tail, m) <= (MAX_CLIP_DEPTH as nat));
            } else {
                assert(depth_at(items, 0) == 0);
            }
        }
    }
}

/// `theorem_validated_bounds`.
pub proof fn theorem_validated_bounds()
    ensures
        super::contract::validated_bounds(),
{
    assert forall|before: Masks, items: Seq<Item>|
        masks_ok(before) && (#[trigger] validate(before, items)) is Some implies super::contract::list_is_sound(
        items,
        validate(before, items)->Some_0,
    ) by {
        lemma_walk_sound(before, 0, items);
    }
}

/// Dropping the first item, once it has applied, moves [`masks_at`] along by one.
pub proof fn lemma_masks_at_tail(masks: Masks, items: Seq<Item>, next: Masks, n: nat)
    requires
        items.len() > 0,
        masks_after(masks, items[0]) == Some(next),
        n < items.len(),
    ensures
        super::contract::masks_at(masks, items, n + 1) == super::contract::masks_at(next, items.subrange(1, items.len() as int), n),
    decreases n,
{
    let tail = items.subrange(1, items.len() as int);
    if n > 0 {
        lemma_masks_at_tail(masks, items, next, (n - 1) as nat);
        assert(items[n as int] == tail[n - 1]);
    }
    assert(super::contract::masks_at(masks, items, 0) == masks);
    assert(super::contract::masks_at(next, tail, 0) == next);
}

/// Every mask drawn in a walk that succeeds is live at that point.
pub proof fn lemma_walk_draws(masks: Masks, depth: nat, items: Seq<Item>, i: int)
    requires
        walk(masks, depth, items) is Some,
        0 <= i < items.len(),
        items[i] is DrawMask,
    ensures
        is_live(super::contract::masks_at(masks, items, i as nat), items[i]->DrawMask_id),
    decreases items.len(),
{
    let tail = items.subrange(1, items.len() as int);
    let next = masks_after(masks, items[0])->Some_0;
    let next_depth = clip_after(depth, items[0])->Some_0;
    if i == 0 {
        assert(super::contract::masks_at(masks, items, 0) == masks);
    } else {
        assert(tail[i - 1] == items[i]);
        lemma_walk_draws(next, next_depth, tail, i - 1);
        lemma_masks_at_tail(masks, items, next, (i - 1) as nat);
    }
}

/// `theorem_draws_are_live`.
pub proof fn theorem_draws_are_live()
    ensures
        super::contract::draws_are_live(),
{
    assert forall|before: Masks, items: Seq<Item>, i: int|
        #![trigger validate(before, items), items[i]]
        masks_ok(before)
            && validate(before, items) is Some
            && 0 <= i < items.len()
            && items[i] is DrawMask implies is_live(super::contract::masks_at(before, items, i as nat), items[i]->DrawMask_id) by {
        lemma_walk_draws(before, 0, items, i);
    }
}

} // verus!
