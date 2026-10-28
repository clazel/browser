//! Why the tokenizer terminates ([`super::spec::run`] and
//! [`super::spec::next_token`] are total: `theorem_tokenizer_total`).
//!
//! Every step either consumes at least one input character, or emits the
//! end-of-file token (after which the tokenizer stops), or hands the
//! current input character to another state without consuming it
//! ("reconsume", or a switch that consumes nothing). Those hand-offs never
//! form a cycle: [`rank_of`] goes down along each one. The rank is a table
//! over the 84 states; for the attribute name state it also depends on the
//! next input character, because the attribute name state and the after
//! attribute name state hand characters to each other, but never the same
//! character both ways. So the pair (characters left, rank) goes down
//! lexicographically on every step that does not stop. A cycle among the
//! hand-offs would make one of the per-state lemmas below fail.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The characters left after the position.
pub open spec fn remaining(input: Seq<u32>, t: Tokenizer) -> nat {
    if t.pos <= input.len() {
        (input.len() - t.pos) as nat
    } else {
        0
    }
}

/// The rank of a state, given the next input character (`None` is EOF):
/// every hand-off of a character to another state lowers it.
pub open spec fn rank_of(s: State, c: Option<u32>) -> nat {
    match s {
        State::Data => 0,
        State::Rcdata => 0,
        State::Rawtext => 0,
        State::ScriptData => 0,
        State::Plaintext => 0,
        State::TagOpen => 1,
        State::EndTagOpen => 1,
        State::TagName => 0,
        State::RcdataLessThanSign => 1,
        State::RcdataEndTagOpen => 2,
        State::RcdataEndTagName => 1,
        State::RawtextLessThanSign => 1,
        State::RawtextEndTagOpen => 2,
        State::RawtextEndTagName => 1,
        State::ScriptDataLessThanSign => 1,
        State::ScriptDataEndTagOpen => 2,
        State::ScriptDataEndTagName => 1,
        State::ScriptDataEscapeStart => 1,
        State::ScriptDataEscapeStartDash => 1,
        State::ScriptDataEscaped => 0,
        State::ScriptDataEscapedDash => 0,
        State::ScriptDataEscapedDashDash => 0,
        State::ScriptDataEscapedLessThanSign => 2,
        State::ScriptDataEscapedEndTagOpen => 2,
        State::ScriptDataEscapedEndTagName => 1,
        State::ScriptDataDoubleEscapeStart => 1,
        State::ScriptDataDoubleEscaped => 0,
        State::ScriptDataDoubleEscapedDash => 0,
        State::ScriptDataDoubleEscapedDashDash => 0,
        State::ScriptDataDoubleEscapedLessThanSign => 1,
        State::ScriptDataDoubleEscapeEnd => 1,
        State::BeforeAttributeName => 3,
        State::AttributeName => match c {
            None => 2,
            Some(c) => if is_tab_lf_ff_space(c) || c == 0x2F || c == 0x3E {
                2
            } else {
                0
            },
        },
        State::AfterAttributeName => 1,
        State::BeforeAttributeValue => 1,
        State::AttributeValueDoubleQuoted => 0,
        State::AttributeValueSingleQuoted => 0,
        State::AttributeValueUnquoted => 0,
        State::AfterAttributeValueQuoted => 4,
        State::SelfClosingStartTag => 4,
        State::BogusComment => 0,
        State::MarkupDeclarationOpen => 1,
        State::CommentStart => 1,
        State::CommentStartDash => 1,
        State::Comment => 0,
        State::CommentLessThanSign => 1,
        State::CommentLessThanSignBang => 1,
        State::CommentLessThanSignBangDash => 2,
        State::CommentLessThanSignBangDashDash => 2,
        State::CommentEndDash => 1,
        State::CommentEnd => 1,
        State::CommentEndBang => 1,
        State::Doctype => 1,
        State::BeforeDoctypeName => 0,
        State::DoctypeName => 0,
        State::AfterDoctypeName => 1,
        State::AfterDoctypePublicKeyword => 1,
        State::BeforeDoctypePublicIdentifier => 1,
        State::DoctypePublicIdentifierDoubleQuoted => 0,
        State::DoctypePublicIdentifierSingleQuoted => 0,
        State::AfterDoctypePublicIdentifier => 1,
        State::BetweenDoctypePublicAndSystemIdentifiers => 1,
        State::AfterDoctypeSystemKeyword => 1,
        State::BeforeDoctypeSystemIdentifier => 1,
        State::DoctypeSystemIdentifierDoubleQuoted => 0,
        State::DoctypeSystemIdentifierSingleQuoted => 0,
        State::AfterDoctypeSystemIdentifier => 1,
        State::BogusDoctype => 0,
        State::CdataSection => 0,
        State::CdataSectionBracket => 1,
        State::CdataSectionEnd => 1,
        State::ProcessingInstructionOpen => 3,
        State::ProcessingInstructionTarget => 2,
        State::AfterProcessingInstructionTarget => 1,
        State::ProcessingInstructionData => 0,
        State::ProcessingInstructionQuestionable => 1,
        State::CharacterReference => 3,
        State::NamedCharacterReference => 2,
        State::AmbiguousAmpersand => 1,
        State::NumericCharacterReference => 3,
        State::HexadecimalCharacterReferenceStart => 3,
        State::HexadecimalCharacterReference => 2,
        State::DecimalCharacterReference => 2,
        State::NumericCharacterReferenceEnd => 1,
    }
}

/// The rank of the tokenizer's state at its next input character.
pub open spec fn rank(input: Seq<u32>, t: Tokenizer) -> nat {
    rank_of(t.state, next_char(input, t.pos))
}

/// The step from `t` to `n` stops the tokenizer or lowers (characters
/// left, rank) lexicographically.
pub open spec fn decreases_ok(input: Seq<u32>, t: Tokenizer, n: Tokenizer) -> bool {
    stopped(input, n) || remaining(input, n) < remaining(input, t) || (remaining(input, n) == remaining(
        input,
        t,
    ) && rank(input, n) < rank(input, t))
}

proof fn lemma_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Data,
    ensures
        decreases_ok(input, t, data_state(input, t).0),
{
}

proof fn lemma_rcdata_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Rcdata,
    ensures
        decreases_ok(input, t, rcdata_state(input, t).0),
{
}

proof fn lemma_rawtext_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Rawtext,
    ensures
        decreases_ok(input, t, rawtext_state(input, t).0),
{
}

proof fn lemma_script_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptData,
    ensures
        decreases_ok(input, t, script_data_state(input, t).0),
{
}

proof fn lemma_plaintext_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Plaintext,
    ensures
        decreases_ok(input, t, plaintext_state(input, t).0),
{
}

proof fn lemma_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is TagOpen,
    ensures
        decreases_ok(input, t, tag_open_state(input, t).0),
{
}

proof fn lemma_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is EndTagOpen,
    ensures
        decreases_ok(input, t, end_tag_open_state(input, t).0),
{
}

proof fn lemma_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is TagName,
    ensures
        decreases_ok(input, t, tag_name_state(input, t).0),
{
}

proof fn lemma_rcdata_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RcdataLessThanSign,
    ensures
        decreases_ok(input, t, rcdata_less_than_sign_state(input, t).0),
{
}

proof fn lemma_rcdata_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RcdataEndTagOpen,
    ensures
        decreases_ok(input, t, rcdata_end_tag_open_state(input, t).0),
{
}

proof fn lemma_rcdata_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RcdataEndTagName,
    ensures
        decreases_ok(input, t, rcdata_end_tag_name_state(input, t).0),
{
}

proof fn lemma_rawtext_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RawtextLessThanSign,
    ensures
        decreases_ok(input, t, rawtext_less_than_sign_state(input, t).0),
{
}

proof fn lemma_rawtext_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RawtextEndTagOpen,
    ensures
        decreases_ok(input, t, rawtext_end_tag_open_state(input, t).0),
{
}

proof fn lemma_rawtext_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is RawtextEndTagName,
    ensures
        decreases_ok(input, t, rawtext_end_tag_name_state(input, t).0),
{
}

proof fn lemma_script_data_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataLessThanSign,
    ensures
        decreases_ok(input, t, script_data_less_than_sign_state(input, t).0),
{
}

proof fn lemma_script_data_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEndTagOpen,
    ensures
        decreases_ok(input, t, script_data_end_tag_open_state(input, t).0),
{
}

proof fn lemma_script_data_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEndTagName,
    ensures
        decreases_ok(input, t, script_data_end_tag_name_state(input, t).0),
{
}

proof fn lemma_script_data_escape_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapeStart,
    ensures
        decreases_ok(input, t, script_data_escape_start_state(input, t).0),
{
}

proof fn lemma_script_data_escape_start_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapeStartDash,
    ensures
        decreases_ok(input, t, script_data_escape_start_dash_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscaped,
    ensures
        decreases_ok(input, t, script_data_escaped_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapedDash,
    ensures
        decreases_ok(input, t, script_data_escaped_dash_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapedDashDash,
    ensures
        decreases_ok(input, t, script_data_escaped_dash_dash_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapedLessThanSign,
    ensures
        decreases_ok(input, t, script_data_escaped_less_than_sign_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_end_tag_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapedEndTagOpen,
    ensures
        decreases_ok(input, t, script_data_escaped_end_tag_open_state(input, t).0),
{
}

proof fn lemma_script_data_escaped_end_tag_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataEscapedEndTagName,
    ensures
        decreases_ok(input, t, script_data_escaped_end_tag_name_state(input, t).0),
{
}

proof fn lemma_script_data_double_escape_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapeStart,
    ensures
        decreases_ok(input, t, script_data_double_escape_start_state(input, t).0),
{
}

proof fn lemma_script_data_double_escaped_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscaped,
    ensures
        decreases_ok(input, t, script_data_double_escaped_state(input, t).0),
{
}

proof fn lemma_script_data_double_escaped_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedDash,
    ensures
        decreases_ok(input, t, script_data_double_escaped_dash_state(input, t).0),
{
}

proof fn lemma_script_data_double_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedDashDash,
    ensures
        decreases_ok(input, t, script_data_double_escaped_dash_dash_state(input, t).0),
{
}

proof fn lemma_script_data_double_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedLessThanSign,
    ensures
        decreases_ok(input, t, script_data_double_escaped_less_than_sign_state(input, t).0),
{
}

proof fn lemma_script_data_double_escape_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapeEnd,
    ensures
        decreases_ok(input, t, script_data_double_escape_end_state(input, t).0),
{
}

proof fn lemma_before_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BeforeAttributeName,
    ensures
        decreases_ok(input, t, before_attribute_name_state(input, t).0),
{
}

proof fn lemma_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AttributeName,
    ensures
        decreases_ok(input, t, attribute_name_state(input, t).0),
{
}

proof fn lemma_after_attribute_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterAttributeName,
    ensures
        decreases_ok(input, t, after_attribute_name_state(input, t).0),
{
}

proof fn lemma_before_attribute_value_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BeforeAttributeValue,
    ensures
        decreases_ok(input, t, before_attribute_value_state(input, t).0),
{
}

proof fn lemma_attribute_value_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AttributeValueDoubleQuoted,
    ensures
        decreases_ok(input, t, attribute_value_double_quoted_state(input, t).0),
{
}

proof fn lemma_attribute_value_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AttributeValueSingleQuoted,
    ensures
        decreases_ok(input, t, attribute_value_single_quoted_state(input, t).0),
{
}

proof fn lemma_attribute_value_unquoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AttributeValueUnquoted,
    ensures
        decreases_ok(input, t, attribute_value_unquoted_state(input, t).0),
{
}

proof fn lemma_after_attribute_value_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterAttributeValueQuoted,
    ensures
        decreases_ok(input, t, after_attribute_value_quoted_state(input, t).0),
{
}

proof fn lemma_self_closing_start_tag_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is SelfClosingStartTag,
    ensures
        decreases_ok(input, t, self_closing_start_tag_state(input, t).0),
{
}

proof fn lemma_bogus_comment_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BogusComment,
    ensures
        decreases_ok(input, t, bogus_comment_state(input, t).0),
{
}

proof fn lemma_markup_declaration_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is MarkupDeclarationOpen,
    ensures
        decreases_ok(input, t, markup_declaration_open_state(input, t).0),
{
}

proof fn lemma_comment_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentStart,
    ensures
        decreases_ok(input, t, comment_start_state(input, t).0),
{
}

proof fn lemma_comment_start_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentStartDash,
    ensures
        decreases_ok(input, t, comment_start_dash_state(input, t).0),
{
}

proof fn lemma_comment_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Comment,
    ensures
        decreases_ok(input, t, comment_state(input, t).0),
{
}

proof fn lemma_comment_less_than_sign_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentLessThanSign,
    ensures
        decreases_ok(input, t, comment_less_than_sign_state(input, t).0),
{
}

proof fn lemma_comment_less_than_sign_bang_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentLessThanSignBang,
    ensures
        decreases_ok(input, t, comment_less_than_sign_bang_state(input, t).0),
{
}

proof fn lemma_comment_less_than_sign_bang_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentLessThanSignBangDash,
    ensures
        decreases_ok(input, t, comment_less_than_sign_bang_dash_state(input, t).0),
{
}

proof fn lemma_comment_less_than_sign_bang_dash_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentLessThanSignBangDashDash,
    ensures
        decreases_ok(input, t, comment_less_than_sign_bang_dash_dash_state(input, t).0),
{
}

proof fn lemma_comment_end_dash_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentEndDash,
    ensures
        decreases_ok(input, t, comment_end_dash_state(input, t).0),
{
}

proof fn lemma_comment_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentEnd,
    ensures
        decreases_ok(input, t, comment_end_state(input, t).0),
{
}

proof fn lemma_comment_end_bang_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CommentEndBang,
    ensures
        decreases_ok(input, t, comment_end_bang_state(input, t).0),
{
}

proof fn lemma_doctype_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is Doctype,
    ensures
        decreases_ok(input, t, doctype_state(input, t).0),
{
}

proof fn lemma_before_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BeforeDoctypeName,
    ensures
        decreases_ok(input, t, before_doctype_name_state(input, t).0),
{
}

proof fn lemma_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DoctypeName,
    ensures
        decreases_ok(input, t, doctype_name_state(input, t).0),
{
}

proof fn lemma_after_doctype_name_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterDoctypeName,
    ensures
        decreases_ok(input, t, after_doctype_name_state(input, t).0),
{
}

proof fn lemma_after_doctype_public_keyword_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterDoctypePublicKeyword,
    ensures
        decreases_ok(input, t, after_doctype_public_keyword_state(input, t).0),
{
}

proof fn lemma_before_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BeforeDoctypePublicIdentifier,
    ensures
        decreases_ok(input, t, before_doctype_public_identifier_state(input, t).0),
{
}

proof fn lemma_doctype_public_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DoctypePublicIdentifierDoubleQuoted,
    ensures
        decreases_ok(input, t, doctype_public_identifier_double_quoted_state(input, t).0),
{
}

proof fn lemma_doctype_public_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DoctypePublicIdentifierSingleQuoted,
    ensures
        decreases_ok(input, t, doctype_public_identifier_single_quoted_state(input, t).0),
{
}

proof fn lemma_after_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterDoctypePublicIdentifier,
    ensures
        decreases_ok(input, t, after_doctype_public_identifier_state(input, t).0),
{
}

proof fn lemma_between_doctype_public_and_system_identifiers_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BetweenDoctypePublicAndSystemIdentifiers,
    ensures
        decreases_ok(input, t, between_doctype_public_and_system_identifiers_state(input, t).0),
{
}

proof fn lemma_after_doctype_system_keyword_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterDoctypeSystemKeyword,
    ensures
        decreases_ok(input, t, after_doctype_system_keyword_state(input, t).0),
{
}

proof fn lemma_before_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BeforeDoctypeSystemIdentifier,
    ensures
        decreases_ok(input, t, before_doctype_system_identifier_state(input, t).0),
{
}

proof fn lemma_doctype_system_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DoctypeSystemIdentifierDoubleQuoted,
    ensures
        decreases_ok(input, t, doctype_system_identifier_double_quoted_state(input, t).0),
{
}

proof fn lemma_doctype_system_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DoctypeSystemIdentifierSingleQuoted,
    ensures
        decreases_ok(input, t, doctype_system_identifier_single_quoted_state(input, t).0),
{
}

proof fn lemma_after_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterDoctypeSystemIdentifier,
    ensures
        decreases_ok(input, t, after_doctype_system_identifier_state(input, t).0),
{
}

proof fn lemma_bogus_doctype_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is BogusDoctype,
    ensures
        decreases_ok(input, t, bogus_doctype_state(input, t).0),
{
}

proof fn lemma_cdata_section_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CdataSection,
    ensures
        decreases_ok(input, t, cdata_section_state(input, t).0),
{
}

proof fn lemma_cdata_section_bracket_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CdataSectionBracket,
    ensures
        decreases_ok(input, t, cdata_section_bracket_state(input, t).0),
{
}

proof fn lemma_cdata_section_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CdataSectionEnd,
    ensures
        decreases_ok(input, t, cdata_section_end_state(input, t).0),
{
}

proof fn lemma_processing_instruction_open_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ProcessingInstructionOpen,
    ensures
        decreases_ok(input, t, processing_instruction_open_state(input, t).0),
{
}

proof fn lemma_processing_instruction_target_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ProcessingInstructionTarget,
    ensures
        decreases_ok(input, t, processing_instruction_target_state(input, t).0),
{
}

proof fn lemma_after_processing_instruction_target_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AfterProcessingInstructionTarget,
    ensures
        decreases_ok(input, t, after_processing_instruction_target_state(input, t).0),
{
}

proof fn lemma_processing_instruction_data_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ProcessingInstructionData,
    ensures
        decreases_ok(input, t, processing_instruction_data_state(input, t).0),
{
}

proof fn lemma_processing_instruction_questionable_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is ProcessingInstructionQuestionable,
    ensures
        decreases_ok(input, t, processing_instruction_questionable_state(input, t).0),
{
}

proof fn lemma_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is CharacterReference,
    ensures
        decreases_ok(input, t, character_reference_state(input, t).0),
{
}

proof fn lemma_named_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is NamedCharacterReference,
    ensures
        decreases_ok(input, t, named_character_reference_state(input, t).0),
{
    crate::charref::lemmas::lemma_match_consumes_two(input, t.pos as int);
}

proof fn lemma_ambiguous_ampersand_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is AmbiguousAmpersand,
    ensures
        decreases_ok(input, t, ambiguous_ampersand_state(input, t).0),
{
}

proof fn lemma_numeric_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is NumericCharacterReference,
    ensures
        decreases_ok(input, t, numeric_character_reference_state(input, t).0),
{
}

proof fn lemma_hexadecimal_character_reference_start_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is HexadecimalCharacterReferenceStart,
    ensures
        decreases_ok(input, t, hexadecimal_character_reference_start_state(input, t).0),
{
}

proof fn lemma_hexadecimal_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is HexadecimalCharacterReference,
    ensures
        decreases_ok(input, t, hexadecimal_character_reference_state(input, t).0),
{
}

proof fn lemma_decimal_character_reference_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is DecimalCharacterReference,
    ensures
        decreases_ok(input, t, decimal_character_reference_state(input, t).0),
{
}

proof fn lemma_numeric_character_reference_end_state(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        t.state is NumericCharacterReferenceEnd,
    ensures
        decreases_ok(input, t, numeric_character_reference_end_state(input, t).0),
{
}

/// Every step that does not stop lowers the measure.
pub proof fn lemma_step_decreases(input: Seq<u32>, t: Tokenizer)
    ensures
        !stopped(input, t) ==> decreases_ok(input, t, step(input, t).0),
{
    if !stopped(input, t) {
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
}

/// A call of [`next_token`] that does not start stopped lowers the
/// measure too: it runs one or more steps, each lowering it.
pub proof fn lemma_next_token_decreases(input: Seq<u32>, t: Tokenizer)
    ensures
        !stopped(input, t) ==> decreases_ok(input, t, next_token(input, t).0),
    decreases remaining(input, t), rank(input, t),
{
    if !stopped(input, t) {
        lemma_step_decreases(input, t);
        let (n, toks) = step(input, t);
        if !(toks.len() > 0 || stopped(input, n)) {
            lemma_next_token_decreases(input, n);
        }
    }
}

} // verus!
