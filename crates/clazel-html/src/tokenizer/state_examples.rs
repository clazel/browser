//! Single states evaluated on concrete tokenizers: the named character
//! reference state and the ambiguous ampersand state with an attribute as
//! the return state, which no whole-input example in [`super::examples`]
//! can reach in a form Verus evaluates (the named state reads the
//! 2231-row table). The named state's example is proven, not evaluated:
//! from `crate::charref::examples::lemma_example_notit` (the match is row
//! 1527) and the row's name and code points, evaluated alone.
//!
//! This is a module of its own for the reason `examples.rs` is.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A tokenizer in `state` that met `&` in a double-quoted attribute value.
pub open spec fn in_attribute(state: State) -> Tokenizer {
    Tokenizer {
        return_state: ReturnState::AttributeValueDoubleQuoted,
        temporary_buffer: seq![0x26u32],
        ..initial(state, None)
    }
}

/// §13.2.5.79: in an attribute, an ASCII alphanumeric after an unmatched
/// `&` goes to the attribute's value; no token is emitted.
pub proof fn lemma_ambiguous_ampersand_in_attribute()
    ensures
        ambiguous_ampersand_state(seq![0x78u32], in_attribute(State::AmbiguousAmpersand)).1.len() == 0,
        ambiguous_ampersand_state(seq![0x78u32], in_attribute(State::AmbiguousAmpersand)).0.current_attribute.value
            == seq![0x78u32],
{
    assert(ambiguous_ampersand_state(seq![0x78u32], in_attribute(State::AmbiguousAmpersand)).1.len() == 0)
        by (compute_only);
    assert(ambiguous_ampersand_state(seq![0x78u32], in_attribute(State::AmbiguousAmpersand)).0.current_attribute.value
        == seq![0x78u32]) by (compute_only);
}

/// Row 1527 of the table is named `not`, evaluated alone.
proof fn lemma_row_not_name()
    ensures
        crate::charref::spec::entity_name(1527) == seq![0x6Eu32, 0x6F, 0x74],
{
    reveal(crate::charref::data::ENTITY_NAME_START_0);
    reveal(crate::charref::data::ENTITY_NAME_LEN_0);
    reveal(crate::charref::data::ENTITY_CHARS_11);
    assert(crate::charref::spec::entity_name(1527) == seq![0x6Eu32, 0x6F, 0x74]) by (compute_only);
}

/// Row 1527's code point is U+00AC NOT SIGN, evaluated alone.
proof fn lemma_row_not_code_points()
    ensures
        crate::charref::spec::entity_code_points(1527) == seq![0xACu32],
{
    reveal(crate::charref::data::ENTITY_CP1_0);
    reveal(crate::charref::data::ENTITY_CP2_0);
    assert(crate::charref::spec::entity_code_points(1527) == seq![0xACu32]) by (compute_only);
}

/// Row 1527 of the table is `not` (U+00AC).
pub proof fn lemma_row_not()
    ensures
        crate::charref::spec::entity_name(1527) == seq![0x6Eu32, 0x6F, 0x74],
        crate::charref::spec::entity_code_points(1527) == seq![0xACu32],
{
    lemma_row_not_name();
    lemma_row_not_code_points();
}

/// §13.2.5.78's note, in an attribute: `&notit;` is not a reference, for
/// historical reasons: the matched `&not` goes to the attribute's value as
/// it is (and the tokenizer returns to the attribute value state after
/// `not`).
pub proof fn lemma_named_in_attribute()
    ensures
        crate::charref::spec::longest_match(seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B], 0) == Some(1527nat),
        named_character_reference_state(
            seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B],
            in_attribute(State::NamedCharacterReference),
        ).0.current_attribute.value == seq![0x26u32, 0x6E, 0x6F, 0x74],
{
    crate::charref::examples::lemma_example_notit();
    lemma_row_not();
    let input = seq![0x6Eu32, 0x6F, 0x74, 0x69, 0x74, 0x3B];
    let t = in_attribute(State::NamedCharacterReference);
    let name = crate::charref::spec::entity_name(1527);
    assert(crate::charref::spec::historical_reasons(true, name, Some(0x69u32)));
    assert(next_char(input, 3) == Some(0x69u32));
    assert(t.temporary_buffer + name =~= seq![0x26u32, 0x6E, 0x6F, 0x74]);
    assert(Seq::<u32>::empty() + seq![0x26u32, 0x6E, 0x6F, 0x74] =~= seq![0x26u32, 0x6E, 0x6F, 0x74]);
}

} // verus!
