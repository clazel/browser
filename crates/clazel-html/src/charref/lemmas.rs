//! Facts proven about the character reference spec and its table. They
//! are evidence that the transcription is right, and what the tokenizer's
//! output bound (`crate::tokenizer::lemmas`) rests on:
//! - every row's name is non-empty and lies inside the characters table
//!   (Verus reads the generated table, one revealed chunk at a time);
//! - a match consumes at least two code points (the `&` and a name of at
//!   least one) and emits at most two ([`lemma_match_consumes_two`],
//!   [`lemma_code_points_one_or_two`]);
//! - the match is the longest name that is a prefix ([`lemma_longest`]);
//! - the numeric character reference end state always appends a scalar
//!   value that is not U+0000 ([`lemma_end_code_scalar`]), and treats
//!   every number above 0x10FFFF alike ([`lemma_end_code_cap`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Rows `i ..` of the table have a non-empty name inside `ENTITY_CHARS`
/// (evaluated by Verus on the revealed table: the SMT solver alone exceeds
/// its limit on the 2231-row arrays).
pub open spec fn rows_ok_from(i: nat, end: nat) -> bool
    decreases end - i,
{
    if i >= end || i >= entity_count() {
        true
    } else {
        1 <= super::data::entity_name_len_at(i as int) && super::data::entity_name_start_at(i as int)
            + super::data::entity_name_len_at(i as int) <= super::data::ENTITY_CHARS_LEN && rows_ok_from(i + 1, end)
    }
}

proof fn lemma_rows_ok_from(i: nat, end: nat)
    requires
        rows_ok_from(i, end),
    ensures
        forall|j: int|
            i <= j < end && j < entity_count() ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
    decreases end - i,
{
    if i < end && i < entity_count() {
        lemma_rows_ok_from(i + 1, end);
    }
}

proof fn lemma_rows_0()
    ensures
        forall|j: int|
            0 <= j < 100 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(0, 100)) by (compute_only);
    lemma_rows_ok_from(0, 100);
}

proof fn lemma_rows_100()
    ensures
        forall|j: int|
            100 <= j < 200 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(100, 200)) by (compute_only);
    lemma_rows_ok_from(100, 200);
}

proof fn lemma_rows_200()
    ensures
        forall|j: int|
            200 <= j < 300 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(200, 300)) by (compute_only);
    lemma_rows_ok_from(200, 300);
}

proof fn lemma_rows_300()
    ensures
        forall|j: int|
            300 <= j < 400 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(300, 400)) by (compute_only);
    lemma_rows_ok_from(300, 400);
}

proof fn lemma_rows_400()
    ensures
        forall|j: int|
            400 <= j < 500 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(400, 500)) by (compute_only);
    lemma_rows_ok_from(400, 500);
}

proof fn lemma_rows_500()
    ensures
        forall|j: int|
            500 <= j < 600 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(500, 600)) by (compute_only);
    lemma_rows_ok_from(500, 600);
}

proof fn lemma_rows_600()
    ensures
        forall|j: int|
            600 <= j < 700 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(600, 700)) by (compute_only);
    lemma_rows_ok_from(600, 700);
}

proof fn lemma_rows_700()
    ensures
        forall|j: int|
            700 <= j < 800 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(700, 800)) by (compute_only);
    lemma_rows_ok_from(700, 800);
}

proof fn lemma_rows_800()
    ensures
        forall|j: int|
            800 <= j < 900 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(800, 900)) by (compute_only);
    lemma_rows_ok_from(800, 900);
}

proof fn lemma_rows_900()
    ensures
        forall|j: int|
            900 <= j < 1000 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(900, 1000)) by (compute_only);
    lemma_rows_ok_from(900, 1000);
}

proof fn lemma_rows_1000()
    ensures
        forall|j: int|
            1000 <= j < 1100 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1000, 1100)) by (compute_only);
    lemma_rows_ok_from(1000, 1100);
}

proof fn lemma_rows_1100()
    ensures
        forall|j: int|
            1100 <= j < 1200 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1100, 1200)) by (compute_only);
    lemma_rows_ok_from(1100, 1200);
}

proof fn lemma_rows_1200()
    ensures
        forall|j: int|
            1200 <= j < 1300 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1200, 1300)) by (compute_only);
    lemma_rows_ok_from(1200, 1300);
}

proof fn lemma_rows_1300()
    ensures
        forall|j: int|
            1300 <= j < 1400 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1300, 1400)) by (compute_only);
    lemma_rows_ok_from(1300, 1400);
}

proof fn lemma_rows_1400()
    ensures
        forall|j: int|
            1400 <= j < 1500 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1400, 1500)) by (compute_only);
    lemma_rows_ok_from(1400, 1500);
}

proof fn lemma_rows_1500()
    ensures
        forall|j: int|
            1500 <= j < 1600 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1500, 1600)) by (compute_only);
    lemma_rows_ok_from(1500, 1600);
}

proof fn lemma_rows_1600()
    ensures
        forall|j: int|
            1600 <= j < 1700 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1600, 1700)) by (compute_only);
    lemma_rows_ok_from(1600, 1700);
}

proof fn lemma_rows_1700()
    ensures
        forall|j: int|
            1700 <= j < 1800 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1700, 1800)) by (compute_only);
    lemma_rows_ok_from(1700, 1800);
}

proof fn lemma_rows_1800()
    ensures
        forall|j: int|
            1800 <= j < 1900 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1800, 1900)) by (compute_only);
    lemma_rows_ok_from(1800, 1900);
}

proof fn lemma_rows_1900()
    ensures
        forall|j: int|
            1900 <= j < 2000 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(1900, 2000)) by (compute_only);
    lemma_rows_ok_from(1900, 2000);
}

proof fn lemma_rows_2000()
    ensures
        forall|j: int|
            2000 <= j < 2100 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(2000, 2100)) by (compute_only);
    lemma_rows_ok_from(2000, 2100);
}

proof fn lemma_rows_2100()
    ensures
        forall|j: int|
            2100 <= j < 2200 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(2100, 2200)) by (compute_only);
    lemma_rows_ok_from(2100, 2200);
}

proof fn lemma_rows_2200()
    ensures
        forall|j: int|
            2200 <= j < 2231 ==> 1 <= #[trigger] super::data::entity_name_len_at(j)
                && super::data::entity_name_start_at(j) + super::data::entity_name_len_at(j)
                <= super::data::ENTITY_CHARS_LEN,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(rows_ok_from(2200, 2231)) by (compute_only);
    lemma_rows_ok_from(2200, 2231);
}

/// Every row's name is non-empty, and its characters are inside
/// `ENTITY_CHARS`, as the generator lays them out.
pub proof fn lemma_rows_in_bounds()
    ensures
        forall|i: int|
            0 <= i < entity_count() ==> 1 <= #[trigger] super::data::entity_name_len_at(i)
                && super::data::entity_name_start_at(i) + super::data::entity_name_len_at(i)
                <= super::data::ENTITY_CHARS_LEN,
{
    lemma_rows_0();
    lemma_rows_100();
    lemma_rows_200();
    lemma_rows_300();
    lemma_rows_400();
    lemma_rows_500();
    lemma_rows_600();
    lemma_rows_700();
    lemma_rows_800();
    lemma_rows_900();
    lemma_rows_1000();
    lemma_rows_1100();
    lemma_rows_1200();
    lemma_rows_1300();
    lemma_rows_1400();
    lemma_rows_1500();
    lemma_rows_1600();
    lemma_rows_1700();
    lemma_rows_1800();
    lemma_rows_1900();
    lemma_rows_2000();
    lemma_rows_2100();
    lemma_rows_2200();
}

/// The table has the standard's 2231 rows (HTML §13.5; 106 of them are
/// names without a final semicolon).
pub proof fn lemma_table_size()
    ensures
        entity_count() == 2231,
        super::data::ENTITY_ROWS_WITHOUT_SEMICOLON == 106,
{
}

/// Row `i`'s code points are one or two.
pub proof fn lemma_code_points_one_or_two(i: int)
    ensures
        1 <= entity_code_points(i).len() <= 2,
{
}

/// The row [`longest_match_upto`] gives is one of the rows scanned, and
/// its name is a prefix of the input.
pub proof fn lemma_match_upto_is_prefix(input: Seq<u32>, pos: int, k: nat)
    ensures
        match longest_match_upto(input, pos, k) {
            None => true,
            Some(i) => i < k && is_prefix_at(entity_name(i as int), input, pos),
        },
    decreases k,
{
    if k > 0 {
        lemma_match_upto_is_prefix(input, pos, (k - 1) as nat);
    }
}

/// The match is the longest: no row of `0 .. k` has a longer name that is
/// a prefix, and if no row matches, no name of those rows is a prefix.
pub proof fn lemma_longest_upto(input: Seq<u32>, pos: int, k: nat)
    ensures
        forall|j: int|
            0 <= j < k && is_prefix_at(#[trigger] entity_name(j), input, pos) ==> match longest_match_upto(
                input,
                pos,
                k,
            ) {
                None => false,
                Some(i) => entity_name(j).len() <= entity_name(i as int).len(),
            },
    decreases k,
{
    if k > 0 {
        lemma_longest_upto(input, pos, (k - 1) as nat);
    }
}

/// [`longest_match`] is a row of the table whose name is a prefix, and no
/// row's name that is a prefix is longer.
pub proof fn lemma_longest(input: Seq<u32>, pos: int)
    ensures
        match longest_match(input, pos) {
            None => forall|j: int| 0 <= j < entity_count() ==> !is_prefix_at(#[trigger] entity_name(j), input, pos),
            Some(i) => i < entity_count() && is_prefix_at(entity_name(i as int), input, pos) && forall|j: int|
                0 <= j < entity_count() && is_prefix_at(#[trigger] entity_name(j), input, pos) ==> entity_name(
                    j,
                ).len() <= entity_name(i as int).len(),
        },
{
    lemma_match_upto_is_prefix(input, pos, entity_count());
    lemma_longest_upto(input, pos, entity_count());
}

/// A match consumes at least two code points: the `&` the character
/// reference state put in the temporary buffer, and a name of at least
/// one character that the named character reference state consumes.
pub proof fn lemma_match_consumes_two(input: Seq<u32>, pos: int)
    ensures
        match longest_match(input, pos) {
            None => true,
            Some(i) => 1 + entity_name(i as int).len() >= 2 && pos + entity_name(i as int).len() <= input.len(),
        },
{
    lemma_longest(input, pos);
    lemma_rows_in_bounds();
    if let Some(i) = longest_match(input, pos) {
        assert(1 <= super::data::entity_name_len_at(i as int));
    }
}

/// The numeric character reference end state appends a scalar value other
/// than U+0000 (a surrogate, U+0000 and anything above U+10FFFF become
/// U+FFFD).
pub proof fn lemma_end_code_scalar(code: nat)
    ensures
        0 < numeric_reference_end_code(code) <= 0x10FFFF,
        !(0xD800 <= numeric_reference_end_code(code) <= 0xDFFF),
{
}

/// Every number above 0x10FFFF gives U+FFFD, so a code capped at 0x110000
/// gives what the uncapped code gives.
pub proof fn lemma_end_code_cap(code: nat)
    ensures
        numeric_reference_end_code(code) == numeric_reference_end_code(super::contract::capped_code(code)),
        code > 0x10FFFF ==> numeric_reference_end_code(code) == 0xFFFD,
{
}

} // verus!
