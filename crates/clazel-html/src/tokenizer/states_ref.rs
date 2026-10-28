//! The executable states §13.2.5.69 to §13.2.5.84 (CDATA sections,
//! processing instructions, character references), each proven equal to
//! its spec function. The step comments live in [`super::spec`].

use super::actions::*;
use super::buffer::*;
#[allow(unused_imports)]
use super::spec::*;
use super::states_text::*;
use crate::charref::exec::{
    digit_step, entity_code_points_exec, entity_name_last_exec, entity_name_len_exec,
    longest_match_exec, numeric_reference_end_code_exec,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Is `c` an ASCII digit.
fn is_digit_exec(c: u32) -> (r: bool)
    ensures
        r == crate::charref::spec::is_ascii_digit(c),
{
    matches!(c, 0x30..=0x39)
}

/// Is `c` an ASCII alphanumeric.
fn is_alphanumeric_exec(c: u32) -> (r: bool)
    ensures
        r == crate::charref::spec::is_ascii_alphanumeric(c),
{
    is_digit_exec(c) || is_alpha_exec(c)
}

/// §13.2.5.69 CDATA section state.
pub fn cdata_section_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(cdata_section_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if c == 0x5D {
                t.state = State::CdataSectionBracket;
            } else {
                push_char(out, c);
            }
        },
    }
}

/// §13.2.5.70 CDATA section bracket state.
pub fn cdata_section_bracket_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(cdata_section_bracket_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x5D) => {
            consume(input, t);
            t.state = State::CdataSectionEnd;
        },
        _ => {
            t.state = State::CdataSection;
            push_char(out, 0x5D);
        },
    }
}

/// §13.2.5.71 CDATA section end state.
pub fn cdata_section_end_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(cdata_section_end_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x5D) => {
            consume(input, t);
            push_char(out, 0x5D);
        },
        Some(0x3E) => {
            consume(input, t);
            t.state = State::Data;
        },
        _ => {
            t.state = State::CdataSection;
            push_char(out, 0x5D);
            push_char(out, 0x5D);
        },
    }
}

/// §13.2.5.72 Processing instruction open state.
pub fn processing_instruction_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(processing_instruction_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if is_alpha_exec(c) || c == 0x5F {
                t.state = State::ProcessingInstructionTarget;
            } else {
                convert_temporary_buffer_to_comment_exec(t, Ghost(st));
                t.state = State::BogusComment;
            }
        },
    }
}

/// Whether `a` is an ASCII case-insensitive match for `b` (lowercase).
fn eq_ci_exec(a: &Vec<u32>, b: &[u32]) -> (r: bool)
    ensures
        r == eq_ci(a@, b@),
{
    let ghost m = a@.map_values(|c: u32| ascii_lower(c));
    if a.len() != b.len() {
        assert(m.len() != b@.len());
        return false;
    }
    let mut k: usize = 0;
    while k < a.len()
        invariant
            k <= a.len(),
            a.len() == b.len(),
            m == a@.map_values(|c: u32| ascii_lower(c)),
            forall|j: int| 0 <= j < k ==> m[j] == b@[j],
        decreases a.len() - k,
    {
        let x = at32(a.as_slice(), k);
        let lower = if is_upper_exec(x) {
            // Never overflows: x is at most 0x5A.
            x.saturating_add(0x20)
        } else {
            x
        };
        if lower != at32(b, k) {
            assert(m[k as int] != b@[k as int]);
            return false;
        }
        // Never saturates: k < a.len().
        k = k.saturating_add(1);
    }
    assert(m =~= b@);
    true
}

/// §13.2.5.73 Processing instruction target state.
pub fn processing_instruction_target_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(processing_instruction_target_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) || c == 0x3F || c == 0x3E {
                let xml: [u32; 3] = [0x78, 0x6D, 0x6C];
                let xml_ss: [u32; 14] = [0x78, 0x6D, 0x6C, 0x2D, 0x73, 0x74, 0x79, 0x6C, 0x65, 0x73, 0x68, 0x65, 0x65, 0x74];
                assert(xml@ =~= super::spec::xml());
                assert(xml_ss@ =~= xml_stylesheet());
                if eq_ci_exec(&t.temporary_buffer, xml.as_slice()) || eq_ci_exec(&t.temporary_buffer, xml_ss.as_slice()) {
                    convert_temporary_buffer_to_comment_exec(t, Ghost(st));
                    t.state = State::BogusComment;
                } else {
                    let target = copy(&t.temporary_buffer);
                    t.current = ExecToken::ProcessingInstruction { target, data: Vec::new() };
                    t.state = State::AfterProcessingInstructionTarget;
                }
            } else if is_alphanumeric_exec(c) || c == 0x2D || c == 0x5F {
                consume(input, t);
                t.temporary_buffer.push(c);
            } else {
                convert_temporary_buffer_to_comment_exec(t, Ghost(st));
                t.state = State::BogusComment;
            }
        },
    }
}

/// §13.2.5.74 After processing instruction target state.
pub fn after_processing_instruction_target_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_processing_instruction_target_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_tab_lf_ff_space_exec(c) => {
            consume(input, t);
        },
        _ => {
            t.state = State::ProcessingInstructionData;
        },
    }
}

/// §13.2.5.75 Processing instruction data state.
pub fn processing_instruction_data_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(processing_instruction_data_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if c == 0x3F {
                t.state = State::ProcessingInstructionQuestionable;
            } else if c == 0x3E {
                t.state = State::Data;
                emit_current_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else {
                append_to_pi_data_exec(t, c, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.76 Processing instruction questionable state.
pub fn processing_instruction_questionable_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(processing_instruction_questionable_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if c == 0x3E {
                consume(input, t);
                t.state = State::Data;
                emit_current_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else {
                append_to_pi_data_exec(t, 0x3F, Ghost(st));
                t.state = State::ProcessingInstructionData;
            }
        },
    }
}

/// §13.2.5.77 Character reference state.
pub fn character_reference_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(character_reference_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    let amp = from_slice([0x26u32].as_slice());
    assert(amp@ =~= seq![0x26u32]);
    t.temporary_buffer = amp;
    let ghost s1 = Tokenizer { temporary_buffer: seq![0x26u32], ..st };
    match next_char_exec(input, t.pos) {
        Some(c) if is_alphanumeric_exec(c) => {
            t.state = State::NamedCharacterReference;
        },
        Some(c @ 0x23) => {
            consume(input, t);
            t.temporary_buffer.push(c);
            t.state = State::NumericCharacterReference;
        },
        _ => flush_and_return_exec(t, out, Ghost(s1)),
    }
}

/// §13.2.5.78 Named character reference state.
pub fn named_character_reference_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(named_character_reference_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match longest_match_exec(input, t.pos) {
        Some(i) => {
            proof {
                crate::charref::lemmas::lemma_match_consumes_two(input@, st.pos as int);
                crate::charref::lemmas::lemma_longest(input@, st.pos as int);
            }
            let ghost name = crate::charref::spec::entity_name(i as int);
            let len = entity_name_len_exec(i);
            let last = entity_name_last_exec(i);
            let as_attr = consumed_as_part_of_attribute_exec(t);
            // Append the matched characters, which the input holds at pos.
            let mut k: usize = 0;
            let ghost buf0 = t.temporary_buffer@;
            while k < len
                invariant
                    k <= len,
                    len == name.len(),
                    st.pos + len <= input@.len(),
                    input@.len() == input.len() as nat,
                    t.pos == st.pos,
                    input@.subrange(st.pos as int, st.pos + len) == name,
                    t.temporary_buffer@ == buf0 + name.subrange(0, k as int),
                    super::contract::abstracts(st, (Tokenizer { temporary_buffer: buf0, ..t@ })),
                decreases len - k,
            {
                // Never saturates: pos + k < input.len().
                let x = at32(input, t.pos.saturating_add(k));
                assert(x == name[k as int]);
                t.temporary_buffer.push(x);
                assert(name.subrange(0, k + 1) =~= name.subrange(0, k as int).push(name[k as int]));
                assert(input@.subrange(st.pos as int, st.pos + len)[k as int] == input@[st.pos + k]);
                assert(t.temporary_buffer@ =~= buf0 + name.subrange(0, k + 1));
                k = k.saturating_add(1);
            }
            assert(name.subrange(0, len as int) =~= name);
            assert(buf0 == st.temporary_buffer);
            assert(input@.len() == input.len() as nat);
            // Never saturates: the name is within the input.
            t.pos = t.pos.saturating_add(len);
            let ghost n = Tokenizer { pos: st.pos + name.len(), temporary_buffer: st.temporary_buffer + name, ..st };
            assert(super::contract::abstracts(n, t@));
            let next = next_char_exec(input, t.pos);
            let historical = as_attr && last != 0x3B && match next {
                None => false,
                Some(c) => c == 0x3D || is_alphanumeric_exec(c),
            };
            if historical {
                flush_and_return_exec(t, out, Ghost(n));
            } else {
                t.temporary_buffer = entity_code_points_exec(i);
                flush_and_return_exec(
                    t,
                    out,
                    Ghost(Tokenizer { temporary_buffer: crate::charref::spec::entity_code_points(i as int), ..n }),
                );
            }
        },
        None => {
            flush_exec(t, out, Ghost(st));
            t.state = State::AmbiguousAmpersand;
        },
    }
}

/// §13.2.5.79 Ambiguous ampersand state.
pub fn ambiguous_ampersand_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(ambiguous_ampersand_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_alphanumeric_exec(c) => {
            consume(input, t);
            if consumed_as_part_of_attribute_exec(t) {
                append_to_attribute_value_exec(t, c, Ghost(consumed(st)));
            } else {
                push_char(out, c);
            }
        },
        _ => {
            t.state = return_state_state(&t.return_state);
        },
    }
}

/// §13.2.5.80 Numeric character reference state.
pub fn numeric_character_reference_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(numeric_character_reference_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    t.character_reference_code = 0;
    let ghost s1 = Tokenizer { character_reference_code: 0, ..st };
    match next_char_exec(input, t.pos) {
        Some(c) if c == 0x78 || c == 0x58 => {
            consume(input, t);
            t.temporary_buffer.push(c);
            t.state = State::HexadecimalCharacterReferenceStart;
        },
        Some(c) if is_digit_exec(c) => {
            t.state = State::DecimalCharacterReference;
        },
        _ => flush_and_return_exec(t, out, Ghost(s1)),
    }
}

/// Is `c` an ASCII hex digit.
fn is_hex_digit_exec(c: u32) -> (r: bool)
    ensures
        r == is_ascii_hex_digit(c),
{
    is_digit_exec(c) || matches!(c, 0x41..=0x46 | 0x61..=0x66)
}

/// §13.2.5.81 Hexadecimal character reference start state.
pub fn hexadecimal_character_reference_start_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(hexadecimal_character_reference_start_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_hex_digit_exec(c) => {
            t.state = State::HexadecimalCharacterReference;
        },
        _ => flush_and_return_exec(t, out, Ghost(st)),
    }
}

/// Consume a digit worth `digit` in base `base`: [`add_digit`] on the
/// capped code.
fn add_digit_exec(input: &[u32], t: &mut ExecTokenizer, base: u32, digit: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
        st.pos < input@.len(),
        1 <= base <= 16,
        digit < 16,
    ensures
        super::contract::abstracts(add_digit(consumed(st), base as nat, digit as nat), final(t)@),
{
    consume(input, t);
    t.character_reference_code = digit_step(t.character_reference_code, base, digit);
}

/// §13.2.5.82 Hexadecimal character reference state.
pub fn hexadecimal_character_reference_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(hexadecimal_character_reference_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_digit_exec(c) => {
            // Never saturates: c is an ASCII digit.
            add_digit_exec(input, t, 16, c.saturating_sub(0x30), Ghost(st));
        },
        Some(c) if matches!(c, 0x41..=0x46) => {
            // Never saturates: c is an ASCII upper hex digit.
            add_digit_exec(input, t, 16, c.saturating_sub(0x37), Ghost(st));
        },
        Some(c) if matches!(c, 0x61..=0x66) => {
            // Never saturates: c is an ASCII lower hex digit.
            add_digit_exec(input, t, 16, c.saturating_sub(0x57), Ghost(st));
        },
        Some(0x3B) => {
            consume(input, t);
            t.state = State::NumericCharacterReferenceEnd;
        },
        _ => {
            t.state = State::NumericCharacterReferenceEnd;
        },
    }
}

/// §13.2.5.83 Decimal character reference state.
pub fn decimal_character_reference_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(decimal_character_reference_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_digit_exec(c) => {
            // Never saturates: c is an ASCII digit.
            add_digit_exec(input, t, 10, c.saturating_sub(0x30), Ghost(st));
        },
        Some(0x3B) => {
            consume(input, t);
            t.state = State::NumericCharacterReferenceEnd;
        },
        _ => {
            t.state = State::NumericCharacterReferenceEnd;
        },
    }
}

/// §13.2.5.84 Numeric character reference end state.
pub fn numeric_character_reference_end_state_exec(
    _input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(_input@, st, old(t)@),
    ensures
        post(numeric_character_reference_end_state(_input@, st), final(t)@, old(out)@, final(out)@),
{
    proof {
        crate::charref::lemmas::lemma_end_code_cap(st.character_reference_code);
    }
    let code = numeric_reference_end_code_exec(t.character_reference_code);
    let buf = from_slice([code].as_slice());
    assert(buf@ =~= seq![code]);
    t.temporary_buffer = buf;
    flush_and_return_exec(
        t,
        out,
        Ghost(Tokenizer { temporary_buffer: seq![crate::charref::spec::numeric_reference_end_code(st.character_reference_code)], ..st }),
    );
}

} // verus!
