//! The standard's examples, evaluated on the spec: the note of
//! §13.2.5.78 ("&notit;" and "&notin;"), names with and without a
//! semicolon, two-code-point references, inputs that match nothing, every
//! row of §13.2.5.84's table, and the numeric end state's other cases.
//!
//! Matches are evaluated over the block of rows of the input's first
//! character ([`super::index::lemma_match_in_block`]); this is a module of
//! its own because Verus evaluates every `by (compute_only)` assertion of a
//! module it verifies, so a mutant that breaks an example would otherwise
//! fail every kill certificate placed next to it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


proof fn lemma_example_notit_1446_1488()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1446, 1488) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1446, 1488) == None) by (compute_only);
}

proof fn lemma_example_notit_1488_1530()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1488, 1530) == Some(1527nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1488, 1530) == Some(1527nat)) by (compute_only);
}

proof fn lemma_example_notit_1446_1530_pick()
    ensures
        super::search::pick(None, Some(1527nat)) == Some(1527nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(None, Some(1527nat)) == Some(1527nat)) by (compute_only);
}

proof fn lemma_example_notit_1446_1530()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1446, 1530) == Some(1527nat),
{
    lemma_example_notit_1446_1488();
    lemma_example_notit_1488_1530();
    lemma_example_notit_1446_1530_pick();
}

proof fn lemma_example_notit_1530_1572()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1530, 1572) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1530, 1572) == None) by (compute_only);
}

proof fn lemma_example_notit_1572_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1572, 1614) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1572, 1614) == None) by (compute_only);
}

proof fn lemma_example_notit_1530_1614_pick()
    ensures
        super::search::pick(None, None) == None,
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(None, None) == None) by (compute_only);
}

proof fn lemma_example_notit_1530_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1530, 1614) == None,
{
    lemma_example_notit_1530_1572();
    lemma_example_notit_1572_1614();
    lemma_example_notit_1530_1614_pick();
}

proof fn lemma_example_notit_1446_1614_pick()
    ensures
        super::search::pick(Some(1527nat), None) == Some(1527nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(1527nat), None) == Some(1527nat)) by (compute_only);
}

proof fn lemma_example_notit_1446_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0, 1446, 1614) == Some(1527nat),
{
    lemma_example_notit_1446_1530();
    lemma_example_notit_1530_1614();
    lemma_example_notit_1446_1614_pick();
}

proof fn lemma_example_notit_block()
    ensures
        super::index::match_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0) == (1446nat, 1614nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0) == (1446nat, 1614nat)) by (compute_only);
}

/// §13.2.5.78's note: "I'm &notit; I tell you" matches "not".
pub proof fn lemma_example_notit()
    ensures
        longest_match(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0) == Some(1527nat),
{
    lemma_example_notit_block();
    lemma_example_notit_1446_1614();
    super::index::lemma_match_in_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0);
}

proof fn lemma_example_notin_1446_1488()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1446, 1488) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1446, 1488) == None) by (compute_only);
}

proof fn lemma_example_notin_1488_1530()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1488, 1530) == Some(1529nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1488, 1530) == Some(1529nat)) by (compute_only);
}

proof fn lemma_example_notin_1446_1530_pick()
    ensures
        super::search::pick(None, Some(1529nat)) == Some(1529nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(None, Some(1529nat)) == Some(1529nat)) by (compute_only);
}

proof fn lemma_example_notin_1446_1530()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1446, 1530) == Some(1529nat),
{
    lemma_example_notin_1446_1488();
    lemma_example_notin_1488_1530();
    lemma_example_notin_1446_1530_pick();
}

proof fn lemma_example_notin_1530_1572()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1530, 1572) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1530, 1572) == None) by (compute_only);
}

proof fn lemma_example_notin_1572_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1572, 1614) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1572, 1614) == None) by (compute_only);
}

proof fn lemma_example_notin_1530_1614_pick()
    ensures
        super::search::pick(None, None) == None,
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(None, None) == None) by (compute_only);
}

proof fn lemma_example_notin_1530_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1530, 1614) == None,
{
    lemma_example_notin_1530_1572();
    lemma_example_notin_1572_1614();
    lemma_example_notin_1530_1614_pick();
}

proof fn lemma_example_notin_1446_1614_pick()
    ensures
        super::search::pick(Some(1529nat), None) == Some(1529nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(1529nat), None) == Some(1529nat)) by (compute_only);
}

proof fn lemma_example_notin_1446_1614()
    ensures
        super::search::best_in(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0, 1446, 1614) == Some(1529nat),
{
    lemma_example_notin_1446_1530();
    lemma_example_notin_1530_1614();
    lemma_example_notin_1446_1614_pick();
}

proof fn lemma_example_notin_block()
    ensures
        super::index::match_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0) == (1446nat, 1614nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0) == (1446nat, 1614nat)) by (compute_only);
}

/// §13.2.5.78's note: "I'm &notin; I tell you" matches "notin;".
pub proof fn lemma_example_notin()
    ensures
        longest_match(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0) == Some(1529nat),
{
    lemma_example_notin_block();
    lemma_example_notin_1446_1614();
    super::index::lemma_match_in_block(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x6E, 0x3B], 0);
}

proof fn lemma_example_amp_634_668()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x3B], 0, 634, 668) == Some(657nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x3B], 0, 634, 668) == Some(657nat)) by (compute_only);
}

proof fn lemma_example_amp_668_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x3B], 0, 668, 703) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x3B], 0, 668, 703) == None) by (compute_only);
}

proof fn lemma_example_amp_634_703_pick()
    ensures
        super::search::pick(Some(657nat), None) == Some(657nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(657nat), None) == Some(657nat)) by (compute_only);
}

proof fn lemma_example_amp_634_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x3B], 0, 634, 703) == Some(657nat),
{
    lemma_example_amp_634_668();
    lemma_example_amp_668_703();
    lemma_example_amp_634_703_pick();
}

proof fn lemma_example_amp_block()
    ensures
        super::index::match_block(seq![0x61u32, 0x6D, 0x70, 0x3B], 0) == (634nat, 703nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x61u32, 0x6D, 0x70, 0x3B], 0) == (634nat, 703nat)) by (compute_only);
}

/// "&amp;" matches "amp;".
pub proof fn lemma_example_amp()
    ensures
        longest_match(seq![0x61u32, 0x6D, 0x70, 0x3B], 0) == Some(657nat),
{
    lemma_example_amp_block();
    lemma_example_amp_634_703();
    super::index::lemma_match_in_block(seq![0x61u32, 0x6D, 0x70, 0x3B], 0);
}

proof fn lemma_example_amp_no_semicolon_634_668()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x78], 0, 634, 668) == Some(656nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x78], 0, 634, 668) == Some(656nat)) by (compute_only);
}

proof fn lemma_example_amp_no_semicolon_668_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x78], 0, 668, 703) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x78], 0, 668, 703) == None) by (compute_only);
}

proof fn lemma_example_amp_no_semicolon_634_703_pick()
    ensures
        super::search::pick(Some(656nat), None) == Some(656nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(656nat), None) == Some(656nat)) by (compute_only);
}

proof fn lemma_example_amp_no_semicolon_634_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x6D, 0x70, 0x78], 0, 634, 703) == Some(656nat),
{
    lemma_example_amp_no_semicolon_634_668();
    lemma_example_amp_no_semicolon_668_703();
    lemma_example_amp_no_semicolon_634_703_pick();
}

proof fn lemma_example_amp_no_semicolon_block()
    ensures
        super::index::match_block(seq![0x61u32, 0x6D, 0x70, 0x78], 0) == (634nat, 703nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x61u32, 0x6D, 0x70, 0x78], 0) == (634nat, 703nat)) by (compute_only);
}

/// "&ampx" matches "amp", a name the table lists without a semicolon.
pub proof fn lemma_example_amp_no_semicolon()
    ensures
        longest_match(seq![0x61u32, 0x6D, 0x70, 0x78], 0) == Some(656nat),
{
    lemma_example_amp_no_semicolon_block();
    lemma_example_amp_no_semicolon_634_703();
    super::index::lemma_match_in_block(seq![0x61u32, 0x6D, 0x70, 0x78], 0);
}

proof fn lemma_example_acE_634_668()
    ensures
        super::search::best_in(seq![0x61u32, 0x63, 0x45, 0x3B], 0, 634, 668) == Some(638nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x63, 0x45, 0x3B], 0, 634, 668) == Some(638nat)) by (compute_only);
}

proof fn lemma_example_acE_668_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x63, 0x45, 0x3B], 0, 668, 703) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x61u32, 0x63, 0x45, 0x3B], 0, 668, 703) == None) by (compute_only);
}

proof fn lemma_example_acE_634_703_pick()
    ensures
        super::search::pick(Some(638nat), None) == Some(638nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(638nat), None) == Some(638nat)) by (compute_only);
}

proof fn lemma_example_acE_634_703()
    ensures
        super::search::best_in(seq![0x61u32, 0x63, 0x45, 0x3B], 0, 634, 703) == Some(638nat),
{
    lemma_example_acE_634_668();
    lemma_example_acE_668_703();
    lemma_example_acE_634_703_pick();
}

proof fn lemma_example_acE_block()
    ensures
        super::index::match_block(seq![0x61u32, 0x63, 0x45, 0x3B], 0) == (634nat, 703nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x61u32, 0x63, 0x45, 0x3B], 0) == (634nat, 703nat)) by (compute_only);
}

/// "&acE;" matches "acE;", which has two code points.
pub proof fn lemma_example_acE()
    ensures
        longest_match(seq![0x61u32, 0x63, 0x45, 0x3B], 0) == Some(638nat),
{
    lemma_example_acE_block();
    lemma_example_acE_634_703();
    super::index::lemma_match_in_block(seq![0x61u32, 0x63, 0x45, 0x3B], 0);
}

proof fn lemma_example_NotEqualTilde_314_350()
    ensures
        super::search::best_in(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0, 314, 350) == Some(336nat),
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0, 314, 350) == Some(336nat)) by (compute_only);
}

proof fn lemma_example_NotEqualTilde_350_386()
    ensures
        super::search::best_in(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0, 350, 386) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0, 350, 386) == None) by (compute_only);
}

proof fn lemma_example_NotEqualTilde_314_386_pick()
    ensures
        super::search::pick(Some(336nat), None) == Some(336nat),
{
    reveal(super::data::ENTITY_NAME_LEN_0);
    assert(super::search::pick(Some(336nat), None) == Some(336nat)) by (compute_only);
}

proof fn lemma_example_NotEqualTilde_314_386()
    ensures
        super::search::best_in(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0, 314, 386) == Some(336nat),
{
    lemma_example_NotEqualTilde_314_350();
    lemma_example_NotEqualTilde_350_386();
    lemma_example_NotEqualTilde_314_386_pick();
}

proof fn lemma_example_NotEqualTilde_block()
    ensures
        super::index::match_block(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0) == (314nat, 386nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0) == (314nat, 386nat)) by (compute_only);
}

/// "&NotEqualTilde;" matches "NotEqualTilde;".
pub proof fn lemma_example_NotEqualTilde()
    ensures
        longest_match(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0) == Some(336nat),
{
    lemma_example_NotEqualTilde_block();
    lemma_example_NotEqualTilde_314_386();
    super::index::lemma_match_in_block(seq![0x4Eu32, 0x6F, 0x74, 0x45, 0x71, 0x75, 0x61, 0x6C, 0x54, 0x69, 0x6C, 0x64, 0x65, 0x3B], 0);
}

proof fn lemma_example_q_1744_1755()
    ensures
        super::search::best_in(seq![0x71u32], 0, 1744, 1755) == None,
{
    reveal(super::data::ENTITY_NAME_START_0);
    reveal(super::data::ENTITY_NAME_LEN_0);
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
    assert(super::search::best_in(seq![0x71u32], 0, 1744, 1755) == None) by (compute_only);
}

proof fn lemma_example_q_block()
    ensures
        super::index::match_block(seq![0x71u32], 0) == (1744nat, 1755nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x71u32], 0) == (1744nat, 1755nat)) by (compute_only);
}

/// "&q" matches nothing.
pub proof fn lemma_example_q()
    ensures
        longest_match(seq![0x71u32], 0) == None,
{
    lemma_example_q_block();
    lemma_example_q_1744_1755();
    super::index::lemma_match_in_block(seq![0x71u32], 0);
}

proof fn lemma_example_digit_block()
    ensures
        super::index::match_block(seq![0x39u32], 0) == (0nat, 0nat),
{
    reveal(super::data::ENTITY_FIRST_START_0);
    reveal(super::data::ENTITY_FIRST_END_0);
    assert(super::index::match_block(seq![0x39u32], 0) == (0nat, 0nat)) by (compute_only);
}

/// "&9" matches nothing: no name starts with a digit.
pub proof fn lemma_example_digit()
    ensures
        longest_match(seq![0x39u32], 0) == None,
{
    lemma_example_digit_block();
    super::index::lemma_match_in_block(seq![0x39u32], 0);
}

/// §13.2.5.84's table, every row.
pub proof fn lemma_c1_table()
    ensures
        numeric_reference_end_code(0x80) == 0x20AC,
        numeric_reference_end_code(0x82) == 0x201A,
        numeric_reference_end_code(0x83) == 0x192,
        numeric_reference_end_code(0x84) == 0x201E,
        numeric_reference_end_code(0x85) == 0x2026,
        numeric_reference_end_code(0x86) == 0x2020,
        numeric_reference_end_code(0x87) == 0x2021,
        numeric_reference_end_code(0x88) == 0x2C6,
        numeric_reference_end_code(0x89) == 0x2030,
        numeric_reference_end_code(0x8A) == 0x160,
        numeric_reference_end_code(0x8B) == 0x2039,
        numeric_reference_end_code(0x8C) == 0x152,
        numeric_reference_end_code(0x8E) == 0x17D,
        numeric_reference_end_code(0x91) == 0x2018,
        numeric_reference_end_code(0x92) == 0x2019,
        numeric_reference_end_code(0x93) == 0x201C,
        numeric_reference_end_code(0x94) == 0x201D,
        numeric_reference_end_code(0x95) == 0x2022,
        numeric_reference_end_code(0x96) == 0x2013,
        numeric_reference_end_code(0x97) == 0x2014,
        numeric_reference_end_code(0x98) == 0x2DC,
        numeric_reference_end_code(0x99) == 0x2122,
        numeric_reference_end_code(0x9A) == 0x161,
        numeric_reference_end_code(0x9B) == 0x203A,
        numeric_reference_end_code(0x9C) == 0x153,
        numeric_reference_end_code(0x9E) == 0x17E,
        numeric_reference_end_code(0x9F) == 0x178,
{
}

/// §13.2.5.84's other cases: numbers in 0x80 to 0x9F not in the table stay
/// (a parse error only), U+0000, above U+10FFFF and surrogates become
/// U+FFFD, and controls, whitespace, noncharacters and other code points
/// stay.
pub proof fn lemma_numeric_end_examples()
    ensures
        numeric_reference_end_code(0x81) == 0x81,
        numeric_reference_end_code(0x8D) == 0x8D,
        numeric_reference_end_code(0x8F) == 0x8F,
        numeric_reference_end_code(0x90) == 0x90,
        numeric_reference_end_code(0x9D) == 0x9D,
        numeric_reference_end_code(0x0) == 0xFFFD,
        numeric_reference_end_code(0x110000) == 0xFFFD,
        numeric_reference_end_code(0xD800) == 0xFFFD,
        numeric_reference_end_code(0xDFFF) == 0xFFFD,
        numeric_reference_end_code(0xD) == 0xD,
        numeric_reference_end_code(0x9) == 0x9,
        numeric_reference_end_code(0x1) == 0x1,
        numeric_reference_end_code(0x7F) == 0x7F,
        numeric_reference_end_code(0xFFFE) == 0xFFFE,
        numeric_reference_end_code(0x41) == 0x41,
        numeric_reference_end_code(0x10FFFF) == 0x10FFFF,
{
}

/// §13.2.5.78's attribute rule: "&not" followed by "i" in an attribute is
/// not a reference, followed by ";" it is, and outside an attribute it is.
pub proof fn lemma_historical_reasons_examples()
    ensures
        historical_reasons(true, seq![0x6Eu32, 0x6F, 0x74], Some(0x69u32)),
        historical_reasons(true, seq![0x6Eu32, 0x6F, 0x74], Some(0x3Du32)),
        !historical_reasons(true, seq![0x6Eu32, 0x6F, 0x74], Some(0x3Bu32)),
        !historical_reasons(true, seq![0x6Eu32, 0x6F, 0x74], None),
        !historical_reasons(false, seq![0x6Eu32, 0x6F, 0x74], Some(0x69u32)),
        !historical_reasons(true, seq![0x6Eu32, 0x6F, 0x74, 0x3B], Some(0x69u32)),
{
}

} // verus!
