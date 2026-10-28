//! `theorem_output_bounded`: the character tokens the tokenizer emits are
//! no more than the code points of its input (Phase 4 item 4.6; with
//! 4.5's lemma that a named character reference consumes at least two code
//! points and emits at most two). So the token buffer a page needs is
//! bounded by the page.
//!
//! The invariant: the characters emitted so far, plus [`pending`] (those
//! consumed but held back to be emitted later: the `<` of the tag open
//! state, the `</` and the temporary buffer of the end tag name states,
//! the `]` of the CDATA section bracket states, the temporary buffer of the
//! character reference states), never exceed the characters consumed.
//! [`lemma_step_bounded`] shows every step keeps it, state by state.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The number of character tokens in `toks`.
pub open spec fn char_count(toks: Seq<Token>) -> nat
    decreases toks.len(),
{
    if toks.len() == 0 {
        0
    } else {
        char_count(toks.drop_last()) + if toks.last() is Character {
            1nat
        } else {
            0nat
        }
    }
}

/// Characters consumed and not yet emitted, at most.
pub open spec fn pending(t: Tokenizer) -> nat {
    match t.state {
        State::Data => 0,
        State::Rcdata => 0,
        State::Rawtext => 0,
        State::ScriptData => 0,
        State::Plaintext => 0,
        State::TagOpen => 1,
        State::EndTagOpen => 2,
        State::TagName => 0,
        State::RcdataLessThanSign => 1,
        State::RcdataEndTagOpen => 2 + t.temporary_buffer.len(),
        State::RcdataEndTagName => 2 + t.temporary_buffer.len(),
        State::RawtextLessThanSign => 1,
        State::RawtextEndTagOpen => 2 + t.temporary_buffer.len(),
        State::RawtextEndTagName => 2 + t.temporary_buffer.len(),
        State::ScriptDataLessThanSign => 1,
        State::ScriptDataEndTagOpen => 2 + t.temporary_buffer.len(),
        State::ScriptDataEndTagName => 2 + t.temporary_buffer.len(),
        State::ScriptDataEscapeStart => 0,
        State::ScriptDataEscapeStartDash => 0,
        State::ScriptDataEscaped => 0,
        State::ScriptDataEscapedDash => 0,
        State::ScriptDataEscapedDashDash => 0,
        State::ScriptDataEscapedLessThanSign => 1,
        State::ScriptDataEscapedEndTagOpen => 2 + t.temporary_buffer.len(),
        State::ScriptDataEscapedEndTagName => 2 + t.temporary_buffer.len(),
        State::ScriptDataDoubleEscapeStart => 0,
        State::ScriptDataDoubleEscaped => 0,
        State::ScriptDataDoubleEscapedDash => 0,
        State::ScriptDataDoubleEscapedDashDash => 0,
        State::ScriptDataDoubleEscapedLessThanSign => 0,
        State::ScriptDataDoubleEscapeEnd => 0,
        State::BeforeAttributeName => 0,
        State::AttributeName => 0,
        State::AfterAttributeName => 0,
        State::BeforeAttributeValue => 0,
        State::AttributeValueDoubleQuoted => 0,
        State::AttributeValueSingleQuoted => 0,
        State::AttributeValueUnquoted => 0,
        State::AfterAttributeValueQuoted => 0,
        State::SelfClosingStartTag => 0,
        State::BogusComment => 0,
        State::MarkupDeclarationOpen => 0,
        State::CommentStart => 0,
        State::CommentStartDash => 0,
        State::Comment => 0,
        State::CommentLessThanSign => 0,
        State::CommentLessThanSignBang => 0,
        State::CommentLessThanSignBangDash => 0,
        State::CommentLessThanSignBangDashDash => 0,
        State::CommentEndDash => 0,
        State::CommentEnd => 0,
        State::CommentEndBang => 0,
        State::Doctype => 0,
        State::BeforeDoctypeName => 0,
        State::DoctypeName => 0,
        State::AfterDoctypeName => 0,
        State::AfterDoctypePublicKeyword => 0,
        State::BeforeDoctypePublicIdentifier => 0,
        State::DoctypePublicIdentifierDoubleQuoted => 0,
        State::DoctypePublicIdentifierSingleQuoted => 0,
        State::AfterDoctypePublicIdentifier => 0,
        State::BetweenDoctypePublicAndSystemIdentifiers => 0,
        State::AfterDoctypeSystemKeyword => 0,
        State::BeforeDoctypeSystemIdentifier => 0,
        State::DoctypeSystemIdentifierDoubleQuoted => 0,
        State::DoctypeSystemIdentifierSingleQuoted => 0,
        State::AfterDoctypeSystemIdentifier => 0,
        State::BogusDoctype => 0,
        State::CdataSection => 0,
        State::CdataSectionBracket => 1,
        State::CdataSectionEnd => 2,
        State::ProcessingInstructionOpen => 0,
        State::ProcessingInstructionTarget => 0,
        State::AfterProcessingInstructionTarget => 0,
        State::ProcessingInstructionData => 0,
        State::ProcessingInstructionQuestionable => 0,
        State::CharacterReference => 1,
        State::NamedCharacterReference => t.temporary_buffer.len(),
        State::AmbiguousAmpersand => 0,
        State::NumericCharacterReference => t.temporary_buffer.len(),
        State::HexadecimalCharacterReferenceStart => t.temporary_buffer.len(),
        State::HexadecimalCharacterReference => t.temporary_buffer.len(),
        State::DecimalCharacterReference => t.temporary_buffer.len(),
        State::NumericCharacterReferenceEnd => t.temporary_buffer.len(),
    }
}

/// The current token is never a character token (it is a tag, comment,
/// DOCTYPE or processing instruction token), and the character reference
/// states past the first hold the `&` (and `#`) in the temporary buffer.
pub open spec fn inv(t: Tokenizer) -> bool {
    !(t.current is Character) && ((t.state is NamedCharacterReference || t.state is NumericCharacterReference
        || t.state is HexadecimalCharacterReferenceStart || t.state is HexadecimalCharacterReference
        || t.state is DecimalCharacterReference || t.state is NumericCharacterReferenceEnd) ==> t.temporary_buffer.len()
        >= 1)
}

/// One step keeps the invariant: what it emits plus what the next state
/// holds back (nothing, once the tokenizer is done) is no more than what
/// was held back plus what it consumed.
pub open spec fn bounded_step(t: Tokenizer, s: Step) -> bool {
    inv(s.0) && t.pos <= s.0.pos && char_count(s.1) + (if s.0.done {
        0
    } else {
        pending(s.0)
    }) <= pending(t) + (s.0.pos - t.pos)
}

/// Facts about [`char_count`] the per-state lemmas use.
pub proof fn lemma_char_count_facts()
    ensures
        forall|a: Seq<Token>, b: Seq<Token>| #[trigger] char_count(a + b) == char_count(a) + char_count(b),
        forall|s: Seq<u32>| #[trigger] char_count(chars(s)) == s.len(),
        forall|x: Token| #[trigger] char_count(seq![x]) == if x is Character { 1nat } else { 0nat },
        char_count(Seq::<Token>::empty()) == 0,
        forall|a: Seq<Token>, x: Token| #[trigger] char_count(a.push(x)) == char_count(a) + if x is Character {
            1nat
        } else {
            0nat
        },
        char_count(seq![ch(0x3C), ch(0x2F)]) == 2,
        char_count(seq![ch(0x3C), ch(0x21)]) == 2,
        char_count(seq![ch(0x5D), ch(0x5D)]) == 2,
        char_count(seq![ch(0x3C)].push(Token::EndOfFile)) == 1,
        char_count(seq![ch(0x3C), ch(0x2F)].push(Token::EndOfFile)) == 2,
{
    assert forall|a: Seq<Token>, x: Token| #[trigger] char_count(a.push(x)) == char_count(a) + if x is Character {
        1nat
    } else {
        0nat
    } by {
        assert(a.push(x).drop_last() =~= a);
    }
    assert forall|a: Seq<Token>, b: Seq<Token>| #[trigger] char_count(a + b) == char_count(a) + char_count(b) by {
        lemma_char_count_append(a, b);
    }
    assert forall|s: Seq<u32>| #[trigger] char_count(chars(s)) == s.len() by {
        lemma_char_count_chars(s);
    }
    assert forall|x: Token| #[trigger] char_count(seq![x]) == if x is Character { 1nat } else { 0nat } by {
        assert(seq![x].drop_last() =~= Seq::<Token>::empty());
        assert(char_count(Seq::<Token>::empty()) == 0);
        assert(seq![x].last() == x);
    }
    assert(seq![ch(0x3C), ch(0x2F)] =~= seq![ch(0x3C)].push(ch(0x2F)));
    assert(seq![ch(0x3C), ch(0x21)] =~= seq![ch(0x3C)].push(ch(0x21)));
    assert(seq![ch(0x5D), ch(0x5D)] =~= seq![ch(0x5D)].push(ch(0x5D)));
    assert(seq![ch(0x3C), ch(0x2F)] =~= seq![ch(0x3C)].push(ch(0x2F)));
}

proof fn lemma_char_count_append(a: Seq<Token>, b: Seq<Token>)
    ensures
        char_count(a + b) == char_count(a) + char_count(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_char_count_append(a, b.drop_last());
    }
}

proof fn lemma_char_count_chars(s: Seq<u32>)
    ensures
        char_count(chars(s)) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(chars(s).drop_last() =~= chars(s.drop_last()));
        lemma_char_count_chars(s.drop_last());
    }
}

proof fn lemma_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Data,
        inv(t),
    ensures
        bounded_step(t, data_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rcdata_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Rcdata,
        inv(t),
    ensures
        bounded_step(t, rcdata_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rawtext_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Rawtext,
        inv(t),
    ensures
        bounded_step(t, rawtext_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptData,
        inv(t),
    ensures
        bounded_step(t, script_data_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_plaintext_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Plaintext,
        inv(t),
    ensures
        bounded_step(t, plaintext_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is TagOpen,
        inv(t),
    ensures
        bounded_step(t, tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is EndTagOpen,
        inv(t),
    ensures
        bounded_step(t, end_tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is TagName,
        inv(t),
    ensures
        bounded_step(t, tag_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rcdata_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RcdataLessThanSign,
        inv(t),
    ensures
        bounded_step(t, rcdata_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rcdata_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RcdataEndTagOpen,
        inv(t),
    ensures
        bounded_step(t, rcdata_end_tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rcdata_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RcdataEndTagName,
        inv(t),
    ensures
        bounded_step(t, rcdata_end_tag_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rawtext_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RawtextLessThanSign,
        inv(t),
    ensures
        bounded_step(t, rawtext_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rawtext_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RawtextEndTagOpen,
        inv(t),
    ensures
        bounded_step(t, rawtext_end_tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_rawtext_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is RawtextEndTagName,
        inv(t),
    ensures
        bounded_step(t, rawtext_end_tag_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataLessThanSign,
        inv(t),
    ensures
        bounded_step(t, script_data_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEndTagOpen,
        inv(t),
    ensures
        bounded_step(t, script_data_end_tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEndTagName,
        inv(t),
    ensures
        bounded_step(t, script_data_end_tag_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escape_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapeStart,
        inv(t),
    ensures
        bounded_step(t, script_data_escape_start_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escape_start_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapeStartDash,
        inv(t),
    ensures
        bounded_step(t, script_data_escape_start_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscaped,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapedDash,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapedDashDash,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_dash_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapedLessThanSign,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapedEndTagOpen,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_end_tag_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_escaped_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataEscapedEndTagName,
        inv(t),
    ensures
        bounded_step(t, script_data_escaped_end_tag_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escape_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscapeStart,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escape_start_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escaped_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscaped,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escaped_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escaped_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscapedDash,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escaped_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscapedDashDash,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escaped_dash_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscapedLessThanSign,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escaped_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_script_data_double_escape_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ScriptDataDoubleEscapeEnd,
        inv(t),
    ensures
        bounded_step(t, script_data_double_escape_end_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_before_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BeforeAttributeName,
        inv(t),
    ensures
        bounded_step(t, before_attribute_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AttributeName,
        inv(t),
    ensures
        bounded_step(t, attribute_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterAttributeName,
        inv(t),
    ensures
        bounded_step(t, after_attribute_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_before_attribute_value_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BeforeAttributeValue,
        inv(t),
    ensures
        bounded_step(t, before_attribute_value_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_attribute_value_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AttributeValueDoubleQuoted,
        inv(t),
    ensures
        bounded_step(t, attribute_value_double_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_attribute_value_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AttributeValueSingleQuoted,
        inv(t),
    ensures
        bounded_step(t, attribute_value_single_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_attribute_value_unquoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AttributeValueUnquoted,
        inv(t),
    ensures
        bounded_step(t, attribute_value_unquoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_attribute_value_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterAttributeValueQuoted,
        inv(t),
    ensures
        bounded_step(t, after_attribute_value_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_self_closing_start_tag_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is SelfClosingStartTag,
        inv(t),
    ensures
        bounded_step(t, self_closing_start_tag_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_bogus_comment_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BogusComment,
        inv(t),
    ensures
        bounded_step(t, bogus_comment_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_markup_declaration_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is MarkupDeclarationOpen,
        inv(t),
    ensures
        bounded_step(t, markup_declaration_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentStart,
        inv(t),
    ensures
        bounded_step(t, comment_start_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_start_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentStartDash,
        inv(t),
    ensures
        bounded_step(t, comment_start_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Comment,
        inv(t),
    ensures
        bounded_step(t, comment_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentLessThanSign,
        inv(t),
    ensures
        bounded_step(t, comment_less_than_sign_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_less_than_sign_bang_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentLessThanSignBang,
        inv(t),
    ensures
        bounded_step(t, comment_less_than_sign_bang_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_less_than_sign_bang_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentLessThanSignBangDash,
        inv(t),
    ensures
        bounded_step(t, comment_less_than_sign_bang_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_less_than_sign_bang_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentLessThanSignBangDashDash,
        inv(t),
    ensures
        bounded_step(t, comment_less_than_sign_bang_dash_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_end_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentEndDash,
        inv(t),
    ensures
        bounded_step(t, comment_end_dash_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentEnd,
        inv(t),
    ensures
        bounded_step(t, comment_end_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_comment_end_bang_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CommentEndBang,
        inv(t),
    ensures
        bounded_step(t, comment_end_bang_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is Doctype,
        inv(t),
    ensures
        bounded_step(t, doctype_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_before_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BeforeDoctypeName,
        inv(t),
    ensures
        bounded_step(t, before_doctype_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DoctypeName,
        inv(t),
    ensures
        bounded_step(t, doctype_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterDoctypeName,
        inv(t),
    ensures
        bounded_step(t, after_doctype_name_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_doctype_public_keyword_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterDoctypePublicKeyword,
        inv(t),
    ensures
        bounded_step(t, after_doctype_public_keyword_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_before_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BeforeDoctypePublicIdentifier,
        inv(t),
    ensures
        bounded_step(t, before_doctype_public_identifier_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_public_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DoctypePublicIdentifierDoubleQuoted,
        inv(t),
    ensures
        bounded_step(t, doctype_public_identifier_double_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_public_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DoctypePublicIdentifierSingleQuoted,
        inv(t),
    ensures
        bounded_step(t, doctype_public_identifier_single_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterDoctypePublicIdentifier,
        inv(t),
    ensures
        bounded_step(t, after_doctype_public_identifier_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_between_doctype_public_and_system_identifiers_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BetweenDoctypePublicAndSystemIdentifiers,
        inv(t),
    ensures
        bounded_step(t, between_doctype_public_and_system_identifiers_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_doctype_system_keyword_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterDoctypeSystemKeyword,
        inv(t),
    ensures
        bounded_step(t, after_doctype_system_keyword_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_before_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BeforeDoctypeSystemIdentifier,
        inv(t),
    ensures
        bounded_step(t, before_doctype_system_identifier_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_system_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DoctypeSystemIdentifierDoubleQuoted,
        inv(t),
    ensures
        bounded_step(t, doctype_system_identifier_double_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_doctype_system_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DoctypeSystemIdentifierSingleQuoted,
        inv(t),
    ensures
        bounded_step(t, doctype_system_identifier_single_quoted_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterDoctypeSystemIdentifier,
        inv(t),
    ensures
        bounded_step(t, after_doctype_system_identifier_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_bogus_doctype_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is BogusDoctype,
        inv(t),
    ensures
        bounded_step(t, bogus_doctype_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_cdata_section_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CdataSection,
        inv(t),
    ensures
        bounded_step(t, cdata_section_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_cdata_section_bracket_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CdataSectionBracket,
        inv(t),
    ensures
        bounded_step(t, cdata_section_bracket_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_cdata_section_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CdataSectionEnd,
        inv(t),
    ensures
        bounded_step(t, cdata_section_end_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_processing_instruction_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ProcessingInstructionOpen,
        inv(t),
    ensures
        bounded_step(t, processing_instruction_open_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_processing_instruction_target_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ProcessingInstructionTarget,
        inv(t),
    ensures
        bounded_step(t, processing_instruction_target_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_after_processing_instruction_target_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AfterProcessingInstructionTarget,
        inv(t),
    ensures
        bounded_step(t, after_processing_instruction_target_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_processing_instruction_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ProcessingInstructionData,
        inv(t),
    ensures
        bounded_step(t, processing_instruction_data_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_processing_instruction_questionable_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is ProcessingInstructionQuestionable,
        inv(t),
    ensures
        bounded_step(t, processing_instruction_questionable_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is CharacterReference,
        inv(t),
    ensures
        bounded_step(t, character_reference_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_named_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is NamedCharacterReference,
        inv(t),
    ensures
        bounded_step(t, named_character_reference_state(input, t)),
{
    crate::charref::lemmas::lemma_match_consumes_two(input, t.pos as int);
    if let Some(i) = crate::charref::spec::longest_match(input, t.pos as int) {
        crate::charref::lemmas::lemma_code_points_one_or_two(i as int);
    }
    lemma_char_count_facts();
}

proof fn lemma_ambiguous_ampersand_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is AmbiguousAmpersand,
        inv(t),
    ensures
        bounded_step(t, ambiguous_ampersand_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_numeric_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is NumericCharacterReference,
        inv(t),
    ensures
        bounded_step(t, numeric_character_reference_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_hexadecimal_character_reference_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is HexadecimalCharacterReferenceStart,
        inv(t),
    ensures
        bounded_step(t, hexadecimal_character_reference_start_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_hexadecimal_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is HexadecimalCharacterReference,
        inv(t),
    ensures
        bounded_step(t, hexadecimal_character_reference_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_decimal_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is DecimalCharacterReference,
        inv(t),
    ensures
        bounded_step(t, decimal_character_reference_state(input, t)),
{
    lemma_char_count_facts();
}

proof fn lemma_numeric_character_reference_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.pos <= input.len(),
        t.state is NumericCharacterReferenceEnd,
        inv(t),
    ensures
        bounded_step(t, numeric_character_reference_end_state(input, t)),
{
    lemma_char_count_facts();
}

/// Every step keeps the invariant.
pub proof fn lemma_step_bounded(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        inv(t),
    ensures
        bounded_step(t, step(input, t)),
{
    reveal(step);
    match t.state {
            State::Data => lemma_data_state(input, t),
            State::Rcdata => lemma_rcdata_state(input, t),
            State::Rawtext => lemma_rawtext_state(input, t),
            State::ScriptData => lemma_script_data_state(input, t),
            State::Plaintext => lemma_plaintext_state(input, t),
            State::TagOpen => lemma_tag_open_state(input, t),
            State::EndTagOpen => lemma_end_tag_open_state(input, t),
            State::TagName => lemma_tag_name_state(input, t),
            State::RcdataLessThanSign => lemma_rcdata_less_than_sign_state(input, t),
            State::RcdataEndTagOpen => lemma_rcdata_end_tag_open_state(input, t),
            State::RcdataEndTagName => lemma_rcdata_end_tag_name_state(input, t),
            State::RawtextLessThanSign => lemma_rawtext_less_than_sign_state(input, t),
            State::RawtextEndTagOpen => lemma_rawtext_end_tag_open_state(input, t),
            State::RawtextEndTagName => lemma_rawtext_end_tag_name_state(input, t),
            State::ScriptDataLessThanSign => lemma_script_data_less_than_sign_state(input, t),
            State::ScriptDataEndTagOpen => lemma_script_data_end_tag_open_state(input, t),
            State::ScriptDataEndTagName => lemma_script_data_end_tag_name_state(input, t),
            State::ScriptDataEscapeStart => lemma_script_data_escape_start_state(input, t),
            State::ScriptDataEscapeStartDash => lemma_script_data_escape_start_dash_state(input, t),
            State::ScriptDataEscaped => lemma_script_data_escaped_state(input, t),
            State::ScriptDataEscapedDash => lemma_script_data_escaped_dash_state(input, t),
            State::ScriptDataEscapedDashDash => lemma_script_data_escaped_dash_dash_state(input, t),
            State::ScriptDataEscapedLessThanSign => lemma_script_data_escaped_less_than_sign_state(input, t),
            State::ScriptDataEscapedEndTagOpen => lemma_script_data_escaped_end_tag_open_state(input, t),
            State::ScriptDataEscapedEndTagName => lemma_script_data_escaped_end_tag_name_state(input, t),
            State::ScriptDataDoubleEscapeStart => lemma_script_data_double_escape_start_state(input, t),
            State::ScriptDataDoubleEscaped => lemma_script_data_double_escaped_state(input, t),
            State::ScriptDataDoubleEscapedDash => lemma_script_data_double_escaped_dash_state(input, t),
            State::ScriptDataDoubleEscapedDashDash => lemma_script_data_double_escaped_dash_dash_state(input, t),
            State::ScriptDataDoubleEscapedLessThanSign => lemma_script_data_double_escaped_less_than_sign_state(input, t),
            State::ScriptDataDoubleEscapeEnd => lemma_script_data_double_escape_end_state(input, t),
            State::BeforeAttributeName => lemma_before_attribute_name_state(input, t),
            State::AttributeName => lemma_attribute_name_state(input, t),
            State::AfterAttributeName => lemma_after_attribute_name_state(input, t),
            State::BeforeAttributeValue => lemma_before_attribute_value_state(input, t),
            State::AttributeValueDoubleQuoted => lemma_attribute_value_double_quoted_state(input, t),
            State::AttributeValueSingleQuoted => lemma_attribute_value_single_quoted_state(input, t),
            State::AttributeValueUnquoted => lemma_attribute_value_unquoted_state(input, t),
            State::AfterAttributeValueQuoted => lemma_after_attribute_value_quoted_state(input, t),
            State::SelfClosingStartTag => lemma_self_closing_start_tag_state(input, t),
            State::BogusComment => lemma_bogus_comment_state(input, t),
            State::MarkupDeclarationOpen => lemma_markup_declaration_open_state(input, t),
            State::CommentStart => lemma_comment_start_state(input, t),
            State::CommentStartDash => lemma_comment_start_dash_state(input, t),
            State::Comment => lemma_comment_state(input, t),
            State::CommentLessThanSign => lemma_comment_less_than_sign_state(input, t),
            State::CommentLessThanSignBang => lemma_comment_less_than_sign_bang_state(input, t),
            State::CommentLessThanSignBangDash => lemma_comment_less_than_sign_bang_dash_state(input, t),
            State::CommentLessThanSignBangDashDash => lemma_comment_less_than_sign_bang_dash_dash_state(input, t),
            State::CommentEndDash => lemma_comment_end_dash_state(input, t),
            State::CommentEnd => lemma_comment_end_state(input, t),
            State::CommentEndBang => lemma_comment_end_bang_state(input, t),
            State::Doctype => lemma_doctype_state(input, t),
            State::BeforeDoctypeName => lemma_before_doctype_name_state(input, t),
            State::DoctypeName => lemma_doctype_name_state(input, t),
            State::AfterDoctypeName => lemma_after_doctype_name_state(input, t),
            State::AfterDoctypePublicKeyword => lemma_after_doctype_public_keyword_state(input, t),
            State::BeforeDoctypePublicIdentifier => lemma_before_doctype_public_identifier_state(input, t),
            State::DoctypePublicIdentifierDoubleQuoted => lemma_doctype_public_identifier_double_quoted_state(input, t),
            State::DoctypePublicIdentifierSingleQuoted => lemma_doctype_public_identifier_single_quoted_state(input, t),
            State::AfterDoctypePublicIdentifier => lemma_after_doctype_public_identifier_state(input, t),
            State::BetweenDoctypePublicAndSystemIdentifiers => lemma_between_doctype_public_and_system_identifiers_state(input, t),
            State::AfterDoctypeSystemKeyword => lemma_after_doctype_system_keyword_state(input, t),
            State::BeforeDoctypeSystemIdentifier => lemma_before_doctype_system_identifier_state(input, t),
            State::DoctypeSystemIdentifierDoubleQuoted => lemma_doctype_system_identifier_double_quoted_state(input, t),
            State::DoctypeSystemIdentifierSingleQuoted => lemma_doctype_system_identifier_single_quoted_state(input, t),
            State::AfterDoctypeSystemIdentifier => lemma_after_doctype_system_identifier_state(input, t),
            State::BogusDoctype => lemma_bogus_doctype_state(input, t),
            State::CdataSection => lemma_cdata_section_state(input, t),
            State::CdataSectionBracket => lemma_cdata_section_bracket_state(input, t),
            State::CdataSectionEnd => lemma_cdata_section_end_state(input, t),
            State::ProcessingInstructionOpen => lemma_processing_instruction_open_state(input, t),
            State::ProcessingInstructionTarget => lemma_processing_instruction_target_state(input, t),
            State::AfterProcessingInstructionTarget => lemma_after_processing_instruction_target_state(input, t),
            State::ProcessingInstructionData => lemma_processing_instruction_data_state(input, t),
            State::ProcessingInstructionQuestionable => lemma_processing_instruction_questionable_state(input, t),
            State::CharacterReference => lemma_character_reference_state(input, t),
            State::NamedCharacterReference => lemma_named_character_reference_state(input, t),
            State::AmbiguousAmpersand => lemma_ambiguous_ampersand_state(input, t),
            State::NumericCharacterReference => lemma_numeric_character_reference_state(input, t),
            State::HexadecimalCharacterReferenceStart => lemma_hexadecimal_character_reference_start_state(input, t),
            State::HexadecimalCharacterReference => lemma_hexadecimal_character_reference_state(input, t),
            State::DecimalCharacterReference => lemma_decimal_character_reference_state(input, t),
            State::NumericCharacterReferenceEnd => lemma_numeric_character_reference_end_state(input, t),
    }
}

/// The character tokens of a run from `t` are no more than the code points
/// left after its position, plus those `t` holds back.
pub proof fn lemma_run_bounded(input: Seq<u32>, t: Tokenizer)
    requires
        inv(t),
        t.pos <= input.len(),
    ensures
        char_count(run(input, t)) <= (input.len() - t.pos) + pending(t),
    decreases super::termination::remaining(input, t), super::termination::rank(input, t),
{
    lemma_char_count_facts();
    if !stopped(input, t) {
        super::termination::lemma_step_decreases(input, t);
        lemma_step_bounded(input, t);
        let (n, toks) = step(input, t);
        if !stopped(input, n) {
            lemma_run_bounded(input, n);
        }
    }
}

/// `theorem_output_bounded`: the character data the tokenizer emits is
/// no longer than its input in code points, from any of the states the
/// tests and the tree builder start it in (they hold nothing back).
pub proof fn theorem_output_bounded(input: Seq<u32>, start_state: State, last_start_tag: Option<Seq<u32>>)
    requires
        pending(initial(start_state, last_start_tag)) == 0,
        inv(initial(start_state, last_start_tag)),
    ensures
        char_count(tokenize(input, start_state, last_start_tag)) <= input.len(),
{
    lemma_run_bounded(input, initial(start_state, last_start_tag));
}

} // verus!
