//! The executable tokenizer, proven to meet [`super::contract`]: one
//! step runs the current state's exec function ([`step_exec`]), which is
//! proven equal to its spec function; [`ExecTokenizer::next_token`] runs
//! steps until one emits a token; [`tokenize`] calls it until the
//! tokenizer stops. Both are loops: nothing recurses on the input's
//! length, so the stack is bounded whatever the input.

use super::buffer::*;
#[allow(unused_imports)]
use super::spec::*;
use super::states_markup::*;
use super::states_ref::*;
use super::states_text::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One step: the current state's exec function.
pub fn step_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(g): Ghost<Tokenizer>)
    requires
        pre(input@, g, old(t)@),
    ensures
        post(step(input@, g), final(t)@, old(out)@, final(out)@),
{
    proof {
        reveal(step);
    }
    match t.state {
        State::Data => data_state_exec(input, t, out, Ghost(g)),
        State::Rcdata => rcdata_state_exec(input, t, out, Ghost(g)),
        State::Rawtext => rawtext_state_exec(input, t, out, Ghost(g)),
        State::ScriptData => script_data_state_exec(input, t, out, Ghost(g)),
        State::Plaintext => plaintext_state_exec(input, t, out, Ghost(g)),
        State::TagOpen => tag_open_state_exec(input, t, out, Ghost(g)),
        State::EndTagOpen => end_tag_open_state_exec(input, t, out, Ghost(g)),
        State::TagName => tag_name_state_exec(input, t, out, Ghost(g)),
        State::RcdataLessThanSign => rcdata_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::RcdataEndTagOpen => rcdata_end_tag_open_state_exec(input, t, out, Ghost(g)),
        State::RcdataEndTagName => rcdata_end_tag_name_state_exec(input, t, out, Ghost(g)),
        State::RawtextLessThanSign => rawtext_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::RawtextEndTagOpen => rawtext_end_tag_open_state_exec(input, t, out, Ghost(g)),
        State::RawtextEndTagName => rawtext_end_tag_name_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataLessThanSign => script_data_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEndTagOpen => script_data_end_tag_open_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEndTagName => script_data_end_tag_name_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapeStart => script_data_escape_start_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapeStartDash => script_data_escape_start_dash_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscaped => script_data_escaped_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapedDash => script_data_escaped_dash_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapedDashDash => script_data_escaped_dash_dash_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapedLessThanSign => script_data_escaped_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapedEndTagOpen => script_data_escaped_end_tag_open_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataEscapedEndTagName => script_data_escaped_end_tag_name_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscapeStart => script_data_double_escape_start_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscaped => script_data_double_escaped_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscapedDash => script_data_double_escaped_dash_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscapedDashDash => script_data_double_escaped_dash_dash_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscapedLessThanSign => script_data_double_escaped_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::ScriptDataDoubleEscapeEnd => script_data_double_escape_end_state_exec(input, t, out, Ghost(g)),
        State::BeforeAttributeName => before_attribute_name_state_exec(input, t, out, Ghost(g)),
        State::AttributeName => attribute_name_state_exec(input, t, out, Ghost(g)),
        State::AfterAttributeName => after_attribute_name_state_exec(input, t, out, Ghost(g)),
        State::BeforeAttributeValue => before_attribute_value_state_exec(input, t, out, Ghost(g)),
        State::AttributeValueDoubleQuoted => attribute_value_double_quoted_state_exec(input, t, out, Ghost(g)),
        State::AttributeValueSingleQuoted => attribute_value_single_quoted_state_exec(input, t, out, Ghost(g)),
        State::AttributeValueUnquoted => attribute_value_unquoted_state_exec(input, t, out, Ghost(g)),
        State::AfterAttributeValueQuoted => after_attribute_value_quoted_state_exec(input, t, out, Ghost(g)),
        State::SelfClosingStartTag => self_closing_start_tag_state_exec(input, t, out, Ghost(g)),
        State::BogusComment => bogus_comment_state_exec(input, t, out, Ghost(g)),
        State::MarkupDeclarationOpen => markup_declaration_open_state_exec(input, t, out, Ghost(g)),
        State::CommentStart => comment_start_state_exec(input, t, out, Ghost(g)),
        State::CommentStartDash => comment_start_dash_state_exec(input, t, out, Ghost(g)),
        State::Comment => comment_state_exec(input, t, out, Ghost(g)),
        State::CommentLessThanSign => comment_less_than_sign_state_exec(input, t, out, Ghost(g)),
        State::CommentLessThanSignBang => comment_less_than_sign_bang_state_exec(input, t, out, Ghost(g)),
        State::CommentLessThanSignBangDash => comment_less_than_sign_bang_dash_state_exec(input, t, out, Ghost(g)),
        State::CommentLessThanSignBangDashDash => comment_less_than_sign_bang_dash_dash_state_exec(input, t, out, Ghost(g)),
        State::CommentEndDash => comment_end_dash_state_exec(input, t, out, Ghost(g)),
        State::CommentEnd => comment_end_state_exec(input, t, out, Ghost(g)),
        State::CommentEndBang => comment_end_bang_state_exec(input, t, out, Ghost(g)),
        State::Doctype => doctype_state_exec(input, t, out, Ghost(g)),
        State::BeforeDoctypeName => before_doctype_name_state_exec(input, t, out, Ghost(g)),
        State::DoctypeName => doctype_name_state_exec(input, t, out, Ghost(g)),
        State::AfterDoctypeName => after_doctype_name_state_exec(input, t, out, Ghost(g)),
        State::AfterDoctypePublicKeyword => after_doctype_public_keyword_state_exec(input, t, out, Ghost(g)),
        State::BeforeDoctypePublicIdentifier => before_doctype_public_identifier_state_exec(input, t, out, Ghost(g)),
        State::DoctypePublicIdentifierDoubleQuoted => doctype_public_identifier_double_quoted_state_exec(input, t, out, Ghost(g)),
        State::DoctypePublicIdentifierSingleQuoted => doctype_public_identifier_single_quoted_state_exec(input, t, out, Ghost(g)),
        State::AfterDoctypePublicIdentifier => after_doctype_public_identifier_state_exec(input, t, out, Ghost(g)),
        State::BetweenDoctypePublicAndSystemIdentifiers => between_doctype_public_and_system_identifiers_state_exec(input, t, out, Ghost(g)),
        State::AfterDoctypeSystemKeyword => after_doctype_system_keyword_state_exec(input, t, out, Ghost(g)),
        State::BeforeDoctypeSystemIdentifier => before_doctype_system_identifier_state_exec(input, t, out, Ghost(g)),
        State::DoctypeSystemIdentifierDoubleQuoted => doctype_system_identifier_double_quoted_state_exec(input, t, out, Ghost(g)),
        State::DoctypeSystemIdentifierSingleQuoted => doctype_system_identifier_single_quoted_state_exec(input, t, out, Ghost(g)),
        State::AfterDoctypeSystemIdentifier => after_doctype_system_identifier_state_exec(input, t, out, Ghost(g)),
        State::BogusDoctype => bogus_doctype_state_exec(input, t, out, Ghost(g)),
        State::CdataSection => cdata_section_state_exec(input, t, out, Ghost(g)),
        State::CdataSectionBracket => cdata_section_bracket_state_exec(input, t, out, Ghost(g)),
        State::CdataSectionEnd => cdata_section_end_state_exec(input, t, out, Ghost(g)),
        State::ProcessingInstructionOpen => processing_instruction_open_state_exec(input, t, out, Ghost(g)),
        State::ProcessingInstructionTarget => processing_instruction_target_state_exec(input, t, out, Ghost(g)),
        State::AfterProcessingInstructionTarget => after_processing_instruction_target_state_exec(input, t, out, Ghost(g)),
        State::ProcessingInstructionData => processing_instruction_data_state_exec(input, t, out, Ghost(g)),
        State::ProcessingInstructionQuestionable => processing_instruction_questionable_state_exec(input, t, out, Ghost(g)),
        State::CharacterReference => character_reference_state_exec(input, t, out, Ghost(g)),
        State::NamedCharacterReference => named_character_reference_state_exec(input, t, out, Ghost(g)),
        State::AmbiguousAmpersand => ambiguous_ampersand_state_exec(input, t, out, Ghost(g)),
        State::NumericCharacterReference => numeric_character_reference_state_exec(input, t, out, Ghost(g)),
        State::HexadecimalCharacterReferenceStart => hexadecimal_character_reference_start_state_exec(input, t, out, Ghost(g)),
        State::HexadecimalCharacterReference => hexadecimal_character_reference_state_exec(input, t, out, Ghost(g)),
        State::DecimalCharacterReference => decimal_character_reference_state_exec(input, t, out, Ghost(g)),
        State::NumericCharacterReferenceEnd => numeric_character_reference_end_state_exec(input, t, out, Ghost(g)),
    }
}

impl ExecTokenizer {
    /// The tokenizer before the first step (contract: `new_ensures`).
    pub fn new(start_state: State, last_start_tag: Option<Vec<u32>>) -> (r: ExecTokenizer)
        ensures
            super::contract::new_ensures(start_state, opt_view(last_start_tag), r@),
    {
        let r = ExecTokenizer {
            state: start_state,
            return_state: ReturnState::Data,
            temporary_buffer: Vec::new(),
            character_reference_code: 0,
            current: ExecToken::Comment { data: Vec::new() },
            current_attribute: ExecAttribute { name: Vec::new(), value: Vec::new() },
            attribute_status: AttributeStatus::NoAttribute,
            last_start_tag,
            in_foreign_content: false,
            pos: 0,
            done: false,
        };
        assert(r@.current =~~= empty_comment());
        assert(r@.current_attribute =~~= empty_attribute());
        assert(r@ =~~= initial(start_state, opt_view(last_start_tag)));
        r
    }

    /// Whether the tokenizer has stopped.
    pub fn stopped(&self, input: &[u32]) -> (r: bool)
        ensures
            r == stopped(input@, self@),
    {
        self.done || self.pos > input.len()
    }

    /// The one-token face: steps until one emits a token or the tokenizer
    /// stops (contract: `next_token_requires`, `next_token_ensures`).
    pub fn next_token(&mut self, input: &[u32], Ghost(st): Ghost<Tokenizer>) -> (out: Vec<ExecToken>)
        requires
            super::contract::next_token_requires(input@, st, old(self)@),
        ensures
            super::contract::next_token_ensures(input@, st, final(self)@, tokens_view(out@)),
    {
        proof {
            super::termination::lemma_next_token_decreases(input@, st);
        }
        let mut out: Vec<ExecToken> = Vec::new();
        let ghost mut g = st;
        loop
            invariant
                super::contract::abstracts(g, self@),
                super::contract::wf(input@, g),
                out@.len() == 0,
                next_token(input@, st) == next_token(input@, g),
            decreases super::termination::remaining(input@, g), super::termination::rank(input@, g),
        {
            if self.stopped(input) {
                assert(tokens_view(out@) =~= Seq::<Token>::empty());
                return out;
            }
            proof {
                super::termination::lemma_step_decreases(input@, g);
            }
            step_exec(input, self, &mut out, Ghost(g));
            let ghost n = step(input@, g).0;
            if !out.is_empty() || self.stopped(input) {
                proof {
                    super::termination::lemma_next_token_decreases(input@, g);
                }
                assert(tokens_view(out@) =~= step(input@, g).1);
                return out;
            }
            proof {
                assert(step(input@, g).1.len() == 0);
                g = n;
            }
        }
    }
}

/// The whole-input face: the tokens of `input` from `start_state`, with
/// `last_start_tag` (contract: `tokenize_ensures`), computed as the fold
/// of [`ExecTokenizer::next_token`].
pub fn tokenize(input: &[u32], start_state: State, last_start_tag: Option<Vec<u32>>) -> (out: Vec<ExecToken>)
    ensures
        super::contract::tokenize_ensures(input@, start_state, opt_view(last_start_tag), tokens_view(out@)),
{
    let ghost g0 = initial(start_state, opt_view(last_start_tag));
    let mut t = ExecTokenizer::new(start_state, last_start_tag);
    let mut out: Vec<ExecToken> = Vec::new();
    let ghost mut g = g0;
    proof {
        crate::charref::lemmas::lemma_end_code_cap(0);
        assert(super::contract::abstracts(g0, t@));
    }
    loop
        invariant
            super::contract::abstracts(g, t@),
            super::contract::wf(input@, g),
            tokens_view(out@) + super::contract::fold_next_token(input@, g) == super::contract::fold_next_token(input@, g0),
        ensures
            tokens_view(out@) == super::contract::fold_next_token(input@, g0),
        decreases super::termination::remaining(input@, g), super::termination::rank(input@, g),
    {
        if t.stopped(input) {
            assert(super::contract::fold_next_token(input@, g) == Seq::<Token>::empty());
            assert(tokens_view(out@) + Seq::<Token>::empty() =~= tokens_view(out@));
            break;
        }
        proof {
            super::termination::lemma_next_token_decreases(input@, g);
        }
        let toks = t.next_token(input, Ghost(g));
        let ghost n = next_token(input@, g).0;
        let ghost before = tokens_view(out@);
        let mut toks = toks;
        let ghost tv = tokens_view(toks@);
        out.append(&mut toks);
        assert(tokens_view(out@) =~= before + tv);
        proof {
            if stopped(input@, n) {
                assert(super::contract::fold_next_token(input@, g) == tv);
                assert(super::contract::fold_next_token(input@, n) == Seq::<Token>::empty());
                assert(before + tv + Seq::<Token>::empty() =~= before + tv);
            } else {
                assert(super::contract::fold_next_token(input@, g) == tv + super::contract::fold_next_token(input@, n));
                assert(before + (tv + super::contract::fold_next_token(input@, n)) =~= (before + tv) + super::contract::fold_next_token(input@, n));
            }
            g = n;
        }
        if t.stopped(input) {
            assert(super::contract::fold_next_token(input@, g) == Seq::<Token>::empty());
            assert(tokens_view(out@) + Seq::<Token>::empty() =~= tokens_view(out@));
            break;
        }
    }
    proof {
        super::lemmas::theorem_step_equals_whole(input@, g0);
    }
    out
}

/// §13.2.3.5's newline normalization (contract: `preprocess_ensures`).
pub fn preprocess_exec(input: &[u32]) -> (out: Vec<u32>)
    ensures
        super::contract::preprocess_ensures(input@, out@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    assert(input@.subrange(0, input@.len() as int) =~= input@);
    while i < input.len()
        invariant
            i <= input.len(),
            out@ + preprocess(input@.subrange(i as int, input@.len() as int)) == preprocess(input@),
        decreases input.len() - i,
    {
        let ghost rest = input@.subrange(i as int, input@.len() as int);
        let c = super::buffer::at32(input, i);
        // Never saturates: i < input.len().
        let next = i.saturating_add(1);
        if c == 0x0D && next < input.len() && super::buffer::at32(input, next) == 0x0A {
            out.push(0x0A);
            assert(rest.subrange(2, rest.len() as int) =~= input@.subrange(i + 2, input@.len() as int));
            assert(out@ + preprocess(input@.subrange(i + 2, input@.len() as int)) =~= out@.drop_last() + (seq![0x0Au32] + preprocess(input@.subrange(i + 2, input@.len() as int))));
            // Never saturates: next < input.len().
            i = next.saturating_add(1);
        } else {
            out.push(if c == 0x0D { 0x0A } else { c });
            assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, input@.len() as int));
            assert(out@ + preprocess(input@.subrange(i + 1, input@.len() as int)) =~= out@.drop_last() + (seq![out@.last()] + preprocess(input@.subrange(i + 1, input@.len() as int))));
            i = next;
        }
    }
    assert(preprocess(input@.subrange(input@.len() as int, input@.len() as int)) == Seq::<u32>::empty()) by {
        assert(input@.subrange(input@.len() as int, input@.len() as int) =~= Seq::<u32>::empty());
    }
    assert(out@ + Seq::<u32>::empty() =~= out@);
    out
}

} // verus!
