//! The generated first-character index of the table, proven: every row
//! lies in the block of rows its name's first character names
//! ([`lemma_rows_in_blocks`]), so only that block can hold a match
//! ([`lemma_match_in_block`]). The exec matcher scans that block, and
//! Verus evaluates a match on a concrete input over that block alone
//! (the whole table is beyond its evaluator's time limit).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first character of row `i`'s name.
pub open spec fn first_char(i: int) -> nat {
    super::data::entity_chars_at(super::data::entity_name_start_at(i) as int) as nat
}

/// The block of rows for character `c`: `lo .. hi`.
pub open spec fn block_lo(c: nat) -> nat {
    super::data::entity_first_start_at(c as int) as nat
}

/// See [`block_lo`].
pub open spec fn block_hi(c: nat) -> nat {
    super::data::entity_first_end_at(c as int) as nat
}

/// Rows `i .. end` lie in their first character's block.
pub open spec fn in_blocks_from(i: nat, end: nat) -> bool
    decreases end - i,
{
    if i >= end || i >= entity_count() {
        true
    } else {
        first_char(i as int) < 128 && block_lo(first_char(i as int)) <= i < block_hi(first_char(i as int))
            && in_blocks_from(i + 1, end)
    }
}

proof fn lemma_in_blocks_from(i: nat, end: nat)
    requires
        in_blocks_from(i, end),
    ensures
        forall|j: int|
            i <= j < end && j < entity_count() ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j
                < block_hi(first_char(j)),
    decreases end - i,
{
    if i < end && i < entity_count() {
        lemma_in_blocks_from(i + 1, end);
    }
}

/// Every block lies within the table.
pub open spec fn blocks_ok_from(c: nat) -> bool
    decreases 128 - c,
{
    if c >= 128 {
        true
    } else {
        block_lo(c) <= block_hi(c) <= entity_count() && blocks_ok_from(c + 1)
    }
}

proof fn lemma_blocks_ok_from(c: nat)
    requires
        blocks_ok_from(c),
    ensures
        forall|d: nat| c <= d < 128 ==> block_lo(d) <= #[trigger] block_hi(d) <= entity_count(),
    decreases 128 - c,
{
    if c < 128 {
        lemma_blocks_ok_from(c + 1);
    }
}

/// Every block lies within the table.
pub proof fn lemma_blocks_ok()
    ensures
        forall|d: nat| d < 128 ==> block_lo(d) <= #[trigger] block_hi(d) <= entity_count(),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(blocks_ok_from(0)) by (compute_only);
    lemma_blocks_ok_from(0);
}

proof fn lemma_blocks_0()
    ensures
        forall|j: int|
            0 <= j < 100 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(0, 100)) by (compute_only);
    lemma_in_blocks_from(0, 100);
}

proof fn lemma_blocks_100()
    ensures
        forall|j: int|
            100 <= j < 200 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(100, 200)) by (compute_only);
    lemma_in_blocks_from(100, 200);
}

proof fn lemma_blocks_200()
    ensures
        forall|j: int|
            200 <= j < 300 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(200, 300)) by (compute_only);
    lemma_in_blocks_from(200, 300);
}

proof fn lemma_blocks_300()
    ensures
        forall|j: int|
            300 <= j < 400 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(300, 400)) by (compute_only);
    lemma_in_blocks_from(300, 400);
}

proof fn lemma_blocks_400()
    ensures
        forall|j: int|
            400 <= j < 500 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(400, 500)) by (compute_only);
    lemma_in_blocks_from(400, 500);
}

proof fn lemma_blocks_500()
    ensures
        forall|j: int|
            500 <= j < 600 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(500, 600)) by (compute_only);
    lemma_in_blocks_from(500, 600);
}

proof fn lemma_blocks_600()
    ensures
        forall|j: int|
            600 <= j < 700 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(600, 700)) by (compute_only);
    lemma_in_blocks_from(600, 700);
}

proof fn lemma_blocks_700()
    ensures
        forall|j: int|
            700 <= j < 800 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(700, 800)) by (compute_only);
    lemma_in_blocks_from(700, 800);
}

proof fn lemma_blocks_800()
    ensures
        forall|j: int|
            800 <= j < 900 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(800, 900)) by (compute_only);
    lemma_in_blocks_from(800, 900);
}

proof fn lemma_blocks_900()
    ensures
        forall|j: int|
            900 <= j < 1000 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(900, 1000)) by (compute_only);
    lemma_in_blocks_from(900, 1000);
}

proof fn lemma_blocks_1000()
    ensures
        forall|j: int|
            1000 <= j < 1100 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1000, 1100)) by (compute_only);
    lemma_in_blocks_from(1000, 1100);
}

proof fn lemma_blocks_1100()
    ensures
        forall|j: int|
            1100 <= j < 1200 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1100, 1200)) by (compute_only);
    lemma_in_blocks_from(1100, 1200);
}

proof fn lemma_blocks_1200()
    ensures
        forall|j: int|
            1200 <= j < 1300 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1200, 1300)) by (compute_only);
    lemma_in_blocks_from(1200, 1300);
}

proof fn lemma_blocks_1300()
    ensures
        forall|j: int|
            1300 <= j < 1400 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1300, 1400)) by (compute_only);
    lemma_in_blocks_from(1300, 1400);
}

proof fn lemma_blocks_1400()
    ensures
        forall|j: int|
            1400 <= j < 1500 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1400, 1500)) by (compute_only);
    lemma_in_blocks_from(1400, 1500);
}

proof fn lemma_blocks_1500()
    ensures
        forall|j: int|
            1500 <= j < 1600 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1500, 1600)) by (compute_only);
    lemma_in_blocks_from(1500, 1600);
}

proof fn lemma_blocks_1600()
    ensures
        forall|j: int|
            1600 <= j < 1700 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1600, 1700)) by (compute_only);
    lemma_in_blocks_from(1600, 1700);
}

proof fn lemma_blocks_1700()
    ensures
        forall|j: int|
            1700 <= j < 1800 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1700, 1800)) by (compute_only);
    lemma_in_blocks_from(1700, 1800);
}

proof fn lemma_blocks_1800()
    ensures
        forall|j: int|
            1800 <= j < 1900 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1800, 1900)) by (compute_only);
    lemma_in_blocks_from(1800, 1900);
}

proof fn lemma_blocks_1900()
    ensures
        forall|j: int|
            1900 <= j < 2000 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(1900, 2000)) by (compute_only);
    lemma_in_blocks_from(1900, 2000);
}

proof fn lemma_blocks_2000()
    ensures
        forall|j: int|
            2000 <= j < 2100 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(2000, 2100)) by (compute_only);
    lemma_in_blocks_from(2000, 2100);
}

proof fn lemma_blocks_2100()
    ensures
        forall|j: int|
            2100 <= j < 2200 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(2100, 2200)) by (compute_only);
    lemma_in_blocks_from(2100, 2200);
}

proof fn lemma_blocks_2200()
    ensures
        forall|j: int|
            2200 <= j < 2231 ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(first_char(j)),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_CHARS_0);
    reveal(super::data::ENTITY_CHARS_1);
    reveal(super::data::ENTITY_CHARS_2);
    reveal(super::data::ENTITY_CHARS_3);
    reveal(super::data::ENTITY_CHARS_4);
    reveal(super::data::ENTITY_CHARS_5);
    reveal(super::data::ENTITY_CHARS_6);
    reveal(super::data::ENTITY_CHARS_7);
    reveal(super::data::ENTITY_CHARS_8);
    reveal(super::data::ENTITY_CHARS_9);
    reveal(super::data::ENTITY_CHARS_10);
    reveal(super::data::ENTITY_CHARS_11);
    reveal(super::data::ENTITY_CHARS_12);
    reveal(super::data::ENTITY_CHARS_13);
    reveal(super::data::ENTITY_CHARS_14);
    reveal(super::data::ENTITY_CHARS_15);
    reveal(super::data::ENTITY_CHARS_16);
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(in_blocks_from(2200, 2231)) by (compute_only);
    lemma_in_blocks_from(2200, 2231);
}

/// Every row lies in the block of its name's first character.
pub proof fn lemma_rows_in_blocks()
    ensures
        forall|j: int|
            0 <= j < entity_count() ==> #[trigger] first_char(j) < 128 && block_lo(first_char(j)) <= j < block_hi(
                first_char(j),
            ),
{
    lemma_blocks_0();
    lemma_blocks_100();
    lemma_blocks_200();
    lemma_blocks_300();
    lemma_blocks_400();
    lemma_blocks_500();
    lemma_blocks_600();
    lemma_blocks_700();
    lemma_blocks_800();
    lemma_blocks_900();
    lemma_blocks_1000();
    lemma_blocks_1100();
    lemma_blocks_1200();
    lemma_blocks_1300();
    lemma_blocks_1400();
    lemma_blocks_1500();
    lemma_blocks_1600();
    lemma_blocks_1700();
    lemma_blocks_1800();
    lemma_blocks_1900();
    lemma_blocks_2000();
    lemma_blocks_2100();
    lemma_blocks_2200();
}

/// Rows `lo .. hi` hold no super::search::candidate: their super::search::fold is `None`.
proof fn lemma_fold_none(input: Seq<u32>, pos: int, lo: nat, hi: nat)
    requires
        forall|j: nat| lo <= j < hi ==> #[trigger] super::search::candidate(input, pos, j) is None,
    ensures
        super::search::fold(input, pos, lo, hi) is None,
    decreases hi,
{
    if hi > lo {
        lemma_fold_none(input, pos, lo, (hi - 1) as nat);
    }
}

/// The block that can hold a match from `pos` on: the next input
/// character's, or an empty one at EOF or for a character no name starts
/// with.
pub open spec fn match_block(input: Seq<u32>, pos: int) -> (nat, nat) {
    if 0 <= pos < input.len() && input[pos] < 128 {
        (block_lo(input[pos] as nat), block_hi(input[pos] as nat))
    } else {
        (0, 0)
    }
}

/// Only the block of the next input character can hold a match.
pub proof fn lemma_match_in_block(input: Seq<u32>, pos: int)
    ensures
        match_block(input, pos).0 <= match_block(input, pos).1 <= entity_count(),
        longest_match(input, pos) == super::search::fold(input, pos, match_block(input, pos).0, match_block(input, pos).1),
        longest_match(input, pos) == super::search::best_in(input, pos, match_block(input, pos).0, match_block(input, pos).1),
{
    let (lo, hi) = match_block(input, pos);
    lemma_rows_in_blocks();
    lemma_blocks_ok();
    super::lemmas::lemma_rows_in_bounds();
    let n = entity_count();
    assert forall|j: nat| j < n && !(lo <= j < hi) implies #[trigger] super::search::candidate(input, pos, j) is None by {
        if is_prefix_at(entity_name(j as int), input, pos) {
            assert(entity_name(j as int).len() >= 1);
            assert(input.subrange(pos, pos + entity_name(j as int).len())[0] == entity_name(j as int)[0]);
            assert(input[pos] as nat == first_char(j as int));
        }
    }
    lemma_fold_none(input, pos, 0, lo);
    lemma_fold_none(input, pos, hi, n);
    super::search::lemma_fold_split_pub(input, pos, 0, lo, n);
    super::search::lemma_fold_split_pub(input, pos, lo, hi, n);
    super::search::lemma_best_in_fold_pub(input, pos, lo, hi);
    super::search::lemma_best_in_fold_pub(input, pos, 0, n);
    super::search::lemma_best_in_full(input, pos);
}

} // verus!
