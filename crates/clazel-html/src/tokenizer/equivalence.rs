//! The W3C HTML 5.2 transcription ([`super::independent`]) proven to
//! give the same tokens as the living standard's ([`super::spec`]) on the
//! inputs where the two texts describe the same steps:
//! [`theorem_w3c_equivalent`].
//!
//! The domain, [`in_domain`], leaves out the inputs where the texts
//! differ, each listed with the difference:
//! - no `&`: the character reference states were restructured after W3C
//!   HTML 5.2 (W3C has a character reference end state and a decimal
//!   character reference start state, the living standard an ambiguous
//!   ampersand state), and W3C §8.2.4.77 multiplies decimal digits by 16
//!   (docs/ERRATA.md);
//! - no `<` followed by `?`: the living standard's processing instruction
//!   states (§13.2.5.72 to §13.2.5.76) are new; W3C makes a bogus comment;
//! - no `[CDATA[`: in HTML content both make a bogus comment of
//!   `<![CDATA[...`, with the same tokens, but the living standard
//!   consumes `[CDATA[` in one step and W3C one character at a time, so
//!   the steps do not correspond (the tokens agree on every such input
//!   compared in `agreement.rs`).
//!
//! The two tokenizers are related ([`related`]) when they are in the same
//! state at the same position with the same temporary buffer, last start
//! tag and foreign-content flag, and, in the states where the current token
//! or attribute is read before it is next replaced ([`live_token`],
//! [`live_tag`]), with the same current token and corresponding current
//! attribute. Elsewhere they may differ (W3C's current token before any is
//! created is an end-of-file placeholder; after emitting a tag W3C keeps
//! the tag with its last attribute, the living standard's transcription the
//! tag without it), and neither transcription reads them. One lemma per
//! state shows that related tokenizers take related steps that emit the
//! same tokens; [`theorem_w3c_equivalent`] follows by induction on the run.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The inputs where the texts describe the same steps (see the header).
pub open spec fn in_domain(input: Seq<u32>) -> bool {
    (forall|i: int| 0 <= i < input.len() ==> #[trigger] input[i] != 0x26) && (forall|i: int|
        0 <= i < input.len() - 1 && #[trigger] input[i] == 0x3C ==> input[i + 1] != 0x3F) && (forall|i: nat|
        !#[trigger] starts_with(input, i, cdata_open()))
}

/// The W3C state with the same name.
pub open spec fn w3c_state(s: State) -> Option<super::independent::W3cState> {
    match s {
        State::Data => Some(super::independent::W3cState::Data),
        State::Rcdata => Some(super::independent::W3cState::Rcdata),
        State::Rawtext => Some(super::independent::W3cState::Rawtext),
        State::ScriptData => Some(super::independent::W3cState::ScriptData),
        State::Plaintext => Some(super::independent::W3cState::Plaintext),
        State::TagOpen => Some(super::independent::W3cState::TagOpen),
        State::EndTagOpen => Some(super::independent::W3cState::EndTagOpen),
        State::TagName => Some(super::independent::W3cState::TagName),
        State::RcdataLessThanSign => Some(super::independent::W3cState::RcdataLessThanSign),
        State::RcdataEndTagOpen => Some(super::independent::W3cState::RcdataEndTagOpen),
        State::RcdataEndTagName => Some(super::independent::W3cState::RcdataEndTagName),
        State::RawtextLessThanSign => Some(super::independent::W3cState::RawtextLessThanSign),
        State::RawtextEndTagOpen => Some(super::independent::W3cState::RawtextEndTagOpen),
        State::RawtextEndTagName => Some(super::independent::W3cState::RawtextEndTagName),
        State::ScriptDataLessThanSign => Some(super::independent::W3cState::ScriptDataLessThanSign),
        State::ScriptDataEndTagOpen => Some(super::independent::W3cState::ScriptDataEndTagOpen),
        State::ScriptDataEndTagName => Some(super::independent::W3cState::ScriptDataEndTagName),
        State::ScriptDataEscapeStart => Some(super::independent::W3cState::ScriptDataEscapeStart),
        State::ScriptDataEscapeStartDash => Some(super::independent::W3cState::ScriptDataEscapeStartDash),
        State::ScriptDataEscaped => Some(super::independent::W3cState::ScriptDataEscaped),
        State::ScriptDataEscapedDash => Some(super::independent::W3cState::ScriptDataEscapedDash),
        State::ScriptDataEscapedDashDash => Some(super::independent::W3cState::ScriptDataEscapedDashDash),
        State::ScriptDataEscapedLessThanSign => Some(super::independent::W3cState::ScriptDataEscapedLessThanSign),
        State::ScriptDataEscapedEndTagOpen => Some(super::independent::W3cState::ScriptDataEscapedEndTagOpen),
        State::ScriptDataEscapedEndTagName => Some(super::independent::W3cState::ScriptDataEscapedEndTagName),
        State::ScriptDataDoubleEscapeStart => Some(super::independent::W3cState::ScriptDataDoubleEscapeStart),
        State::ScriptDataDoubleEscaped => Some(super::independent::W3cState::ScriptDataDoubleEscaped),
        State::ScriptDataDoubleEscapedDash => Some(super::independent::W3cState::ScriptDataDoubleEscapedDash),
        State::ScriptDataDoubleEscapedDashDash => Some(super::independent::W3cState::ScriptDataDoubleEscapedDashDash),
        State::ScriptDataDoubleEscapedLessThanSign => Some(super::independent::W3cState::ScriptDataDoubleEscapedLessThanSign),
        State::ScriptDataDoubleEscapeEnd => Some(super::independent::W3cState::ScriptDataDoubleEscapeEnd),
        State::BeforeAttributeName => Some(super::independent::W3cState::BeforeAttributeName),
        State::AttributeName => Some(super::independent::W3cState::AttributeName),
        State::AfterAttributeName => Some(super::independent::W3cState::AfterAttributeName),
        State::BeforeAttributeValue => Some(super::independent::W3cState::BeforeAttributeValue),
        State::AttributeValueDoubleQuoted => Some(super::independent::W3cState::AttributeValueDoubleQuoted),
        State::AttributeValueSingleQuoted => Some(super::independent::W3cState::AttributeValueSingleQuoted),
        State::AttributeValueUnquoted => Some(super::independent::W3cState::AttributeValueUnquoted),
        State::AfterAttributeValueQuoted => Some(super::independent::W3cState::AfterAttributeValueQuoted),
        State::SelfClosingStartTag => Some(super::independent::W3cState::SelfClosingStartTag),
        State::BogusComment => Some(super::independent::W3cState::BogusComment),
        State::MarkupDeclarationOpen => Some(super::independent::W3cState::MarkupDeclarationOpen),
        State::CommentStart => Some(super::independent::W3cState::CommentStart),
        State::CommentStartDash => Some(super::independent::W3cState::CommentStartDash),
        State::Comment => Some(super::independent::W3cState::Comment),
        State::CommentLessThanSign => Some(super::independent::W3cState::CommentLessThanSign),
        State::CommentLessThanSignBang => Some(super::independent::W3cState::CommentLessThanSignBang),
        State::CommentLessThanSignBangDash => Some(super::independent::W3cState::CommentLessThanSignBangDash),
        State::CommentLessThanSignBangDashDash => Some(super::independent::W3cState::CommentLessThanSignBangDashDash),
        State::CommentEndDash => Some(super::independent::W3cState::CommentEndDash),
        State::CommentEnd => Some(super::independent::W3cState::CommentEnd),
        State::CommentEndBang => Some(super::independent::W3cState::CommentEndBang),
        State::Doctype => Some(super::independent::W3cState::Doctype),
        State::BeforeDoctypeName => Some(super::independent::W3cState::BeforeDoctypeName),
        State::DoctypeName => Some(super::independent::W3cState::DoctypeName),
        State::AfterDoctypeName => Some(super::independent::W3cState::AfterDoctypeName),
        State::AfterDoctypePublicKeyword => Some(super::independent::W3cState::AfterDoctypePublicKeyword),
        State::BeforeDoctypePublicIdentifier => Some(super::independent::W3cState::BeforeDoctypePublicIdentifier),
        State::DoctypePublicIdentifierDoubleQuoted => Some(super::independent::W3cState::DoctypePublicIdentifierDoubleQuoted),
        State::DoctypePublicIdentifierSingleQuoted => Some(super::independent::W3cState::DoctypePublicIdentifierSingleQuoted),
        State::AfterDoctypePublicIdentifier => Some(super::independent::W3cState::AfterDoctypePublicIdentifier),
        State::BetweenDoctypePublicAndSystemIdentifiers => Some(super::independent::W3cState::BetweenDoctypePublicAndSystemIdentifiers),
        State::AfterDoctypeSystemKeyword => Some(super::independent::W3cState::AfterDoctypeSystemKeyword),
        State::BeforeDoctypeSystemIdentifier => Some(super::independent::W3cState::BeforeDoctypeSystemIdentifier),
        State::DoctypeSystemIdentifierDoubleQuoted => Some(super::independent::W3cState::DoctypeSystemIdentifierDoubleQuoted),
        State::DoctypeSystemIdentifierSingleQuoted => Some(super::independent::W3cState::DoctypeSystemIdentifierSingleQuoted),
        State::AfterDoctypeSystemIdentifier => Some(super::independent::W3cState::AfterDoctypeSystemIdentifier),
        State::BogusDoctype => Some(super::independent::W3cState::BogusDoctype),
        State::CdataSection => Some(super::independent::W3cState::CdataSection),
        State::CdataSectionBracket => Some(super::independent::W3cState::CdataSectionBracket),
        State::CdataSectionEnd => Some(super::independent::W3cState::CdataSectionEnd),
        _ => None,
    }
}

/// States where the current tag token's attributes and current attribute
/// are read before the next tag is created.
pub open spec fn live_tag(s: State) -> bool {
    s is TagName || s is BeforeAttributeName || s is AttributeName || s is AfterAttributeName || s is BeforeAttributeValue || s is AttributeValueDoubleQuoted || s is AttributeValueSingleQuoted || s is AttributeValueUnquoted || s is AfterAttributeValueQuoted || s is SelfClosingStartTag || s is RcdataEndTagName || s is RawtextEndTagName || s is ScriptDataEndTagName || s is ScriptDataEscapedEndTagName
}

/// States where the current token is read before the next one is created.
pub open spec fn live_token(s: State) -> bool {
    live_tag(s) || s is BogusComment || s is CommentStart || s is CommentStartDash || s is Comment || s is CommentLessThanSign || s is CommentLessThanSignBang || s is CommentLessThanSignBangDash || s is CommentLessThanSignBangDashDash || s is CommentEndDash || s is CommentEnd || s is CommentEndBang || s is DoctypeName || s is AfterDoctypeName || s is AfterDoctypePublicKeyword || s is BeforeDoctypePublicIdentifier || s is DoctypePublicIdentifierDoubleQuoted || s is DoctypePublicIdentifierSingleQuoted || s is AfterDoctypePublicIdentifier || s is BetweenDoctypePublicAndSystemIdentifiers || s is AfterDoctypeSystemKeyword || s is BeforeDoctypeSystemIdentifier || s is DoctypeSystemIdentifierDoubleQuoted || s is DoctypeSystemIdentifierSingleQuoted || s is AfterDoctypeSystemIdentifier || s is BogusDoctype
}

/// The current attributes correspond.
pub open spec fn attribute_related(w: super::independent::W3cTokenizer, t: Tokenizer) -> bool {
    match t.attribute_status {
        AttributeStatus::NoAttribute => w.current_attribute is None,
        AttributeStatus::Kept => w.current_attribute == Some(t.current_attribute) && !w.current_attribute_removed,
        AttributeStatus::Removed => w.current_attribute == Some(t.current_attribute) && w.current_attribute_removed,
    }
}

/// The two tokenizers stand for the same point of the same run.
pub open spec fn related(w: super::independent::W3cTokenizer, t: Tokenizer) -> bool {
    w3c_state(t.state) == Some(w.state) && w.pos == t.pos && w.done == t.done && w.temporary_buffer
        == t.temporary_buffer && w.last_start_tag_name == t.last_start_tag && w.adjusted_current_node_not_html
        == t.in_foreign_content && (live_token(t.state) ==> w.current_token == t.current) && (live_tag(t.state)
        ==> attribute_related(w, t))
}

/// What holds of the living standard's tokenizer on a domain run: never in
/// a state the domain leaves out, and the tag open state just after a `<`.
pub open spec fn inv_eq(input: Seq<u32>, t: Tokenizer) -> bool {
    w3c_state(t.state) is Some && t.pos <= input.len() && (t.state is TagOpen ==> t.pos >= 1 && input[t.pos - 1]
        == 0x3C) && (t.state is AttributeName ==> t.attribute_status is Kept)
}

/// After our step `s` and W3C's steps that emitted `wtoks` and ended in
/// `w2`: the same tokens, both stop or neither does, and if not, related
/// tokenizers.
pub open spec fn after_ok(input: Seq<u32>, s: Step, wtoks: Seq<Token>, w2: super::independent::W3cTokenizer) -> bool {
    wtoks == s.1 && stopped(input, s.0) == super::independent::w3c_stopped(input, w2) && (!stopped(input, s.0)
        ==> related(w2, s.0) && inv_eq(input, s.0))
}

/// Related steps, one of each.
pub open spec fn step_related(input: Seq<u32>, s: Step, ws: super::independent::W3cStep) -> bool {
    after_ok(input, s, ws.1, ws.0)
}

/// What one step of ours and one of W3C's lead to: related tokenizers after
/// one step each; or after two of ours (which emits nothing first) and one
/// of W3C's; or after one of ours and two of W3C's.
pub open spec fn corresponds(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer) -> bool {
    let s = step(input, t);
    let ws = super::independent::w3c_step(input, w);
    step_related(input, s, ws) || (s.1.len() == 0 && !stopped(input, s.0) && step_related(
        input,
        step(input, s.0),
        ws,
    )) || (!super::independent::w3c_stopped(input, ws.0) && after_ok(
        input,
        s,
        ws.1 + super::independent::w3c_step(input, ws.0).1,
        super::independent::w3c_step(input, ws.0).0,
    ))
}

/// W3C's exact word match from `k` on, as a quantified fact (the length
/// condition outside the quantifier).
pub open spec fn word_from(input: Seq<u32>, pos: nat, w: Seq<u32>, k: nat) -> bool {
    (k < w.len() ==> pos + w.len() <= input.len()) && forall|j: int| k <= j < w.len() ==> input[pos + j] == #[trigger] w[j]
}

/// W3C's case-insensitive word match from `k` on, as a quantified fact.
pub open spec fn word_ci_from(input: Seq<u32>, pos: nat, w: Seq<u32>, k: nat) -> bool {
    (k < w.len() ==> pos + w.len() <= input.len()) && forall|j: int|
        k <= j < w.len() ==> super::independent::w3c_ascii_fold(input[pos + j]) == super::independent::w3c_ascii_fold(
            #[trigger] w[j],
        )
}

/// W3C's exact word match from `k` on.
proof fn lemma_match_word(input: Seq<u32>, pos: nat, w: Seq<u32>, k: nat)
    requires
        k <= w.len(),
    ensures
        super::independent::w3c_match_from(input, pos, w, k) == word_from(input, pos, w, k),
    decreases w.len() - k,
{
    if k < w.len() {
        lemma_match_word(input, pos, w, k + 1);
        assert(super::independent::w3c_match_from(input, pos, w, k) == (pos + k < input.len() && input[(pos + k) as int]
            == w[k as int] && super::independent::w3c_match_from(input, pos, w, k + 1)));
        if word_from(input, pos, w, k) {
            assert(input[(pos + k) as int] == w[k as int]);
        }
        if super::independent::w3c_match_from(input, pos, w, k) {
            if k + 1 == w.len() {
                assert(pos + w.len() <= input.len());
            }
        }
    }
}

/// W3C's ASCII case-insensitive word match from `k` on.
proof fn lemma_match_word_ci(input: Seq<u32>, pos: nat, w: Seq<u32>, k: nat)
    requires
        k <= w.len(),
    ensures
        super::independent::w3c_match_ci_from(input, pos, w, k) == word_ci_from(input, pos, w, k),
    decreases w.len() - k,
{
    if k < w.len() {
        lemma_match_word_ci(input, pos, w, k + 1);
        assert(super::independent::w3c_match_ci_from(input, pos, w, k) == (pos + k < input.len()
            && super::independent::w3c_ascii_fold(input[(pos + k) as int]) == super::independent::w3c_ascii_fold(
            w[k as int],
        ) && super::independent::w3c_match_ci_from(input, pos, w, k + 1)));
        if word_ci_from(input, pos, w, k) {
            assert(super::independent::w3c_ascii_fold(input[(pos + k) as int]) == super::independent::w3c_ascii_fold(w[k as int]));
        }
        if super::independent::w3c_match_ci_from(input, pos, w, k) {
            if k + 1 == w.len() {
                assert(pos + w.len() <= input.len());
            }
        }
    }
}

/// W3C's "the next few characters are" `w` is the living standard's
/// `starts_with`.
pub proof fn lemma_word_at(input: Seq<u32>, pos: nat, w: Seq<u32>)
    ensures
        super::independent::w3c_word_at(input, pos, w) == starts_with(input, pos, w),
{
    lemma_match_word(input, pos, w, 0);
    if pos + w.len() <= input.len() {
        let sub = input.subrange(pos as int, (pos + w.len()) as int);
        if super::independent::w3c_word_at(input, pos, w) {
            assert(sub =~= w);
        } else if sub == w {
            assert forall|j: int| 0 <= j < w.len() implies input[pos + j] == #[trigger] w[j] by {
                assert(sub[j] == input[pos + j]);
            }
        }
    }
}

/// W3C's ASCII case-insensitive match of the uppercase word `w` is the
/// living standard's `starts_with_ci` of its lowercase `l`.
pub proof fn lemma_word_at_ci(input: Seq<u32>, pos: nat, w: Seq<u32>, l: Seq<u32>)
    requires
        w.len() == l.len(),
        forall|j: int| 0 <= j < w.len() ==> super::independent::w3c_ascii_fold(#[trigger] w[j]) == l[j],
    ensures
        super::independent::w3c_word_at_ci(input, pos, w) == starts_with_ci(input, pos, l),
{
    lemma_match_word_ci(input, pos, w, 0);
    if pos + w.len() <= input.len() {
        let sub = input.subrange(pos as int, (pos + w.len()) as int).map_values(|c: u32| ascii_lower(c));
        if super::independent::w3c_word_at_ci(input, pos, w) {
            assert forall|j: int| 0 <= j < l.len() implies sub[j] == l[j] by {
                assert(super::independent::w3c_ascii_fold(input[pos + j]) == super::independent::w3c_ascii_fold(w[j]));
            }
            assert(sub =~= l);
        } else if sub == l {
            assert forall|j: int| 0 <= j < w.len() implies super::independent::w3c_ascii_fold(input[pos + j])
                == super::independent::w3c_ascii_fold(#[trigger] w[j]) by {
                assert(sub[j] == ascii_lower(input[pos + j]));
                assert(super::independent::w3c_ascii_fold(l[j]) == l[j]);
            }
        }
    }
}

/// The three words the DOCTYPE states match, W3C's form and ours.
pub proof fn lemma_words(input: Seq<u32>, pos: nat)
    ensures
        super::independent::w3c_word_at_ci(input, pos, super::independent::w3c_word_doctype()) == starts_with_ci(
            input,
            pos,
            doctype_lower(),
        ),
        super::independent::w3c_word_at_ci(input, pos, super::independent::w3c_word_public()) == starts_with_ci(
            input,
            pos,
            public_lower(),
        ),
        super::independent::w3c_word_at_ci(input, pos, super::independent::w3c_word_system()) == starts_with_ci(
            input,
            pos,
            system_lower(),
        ),
        super::independent::w3c_word_at(input, pos, seq![0x002Du32, 0x002Du32]) == starts_with(input, pos, seq![0x2Du32, 0x2D]),
        super::independent::w3c_word_at(input, pos, super::independent::w3c_word_cdata()) == starts_with(input, pos, cdata_open()),
{
    let d = super::independent::w3c_word_doctype();
    let p = super::independent::w3c_word_public();
    let s = super::independent::w3c_word_system();
    assert forall|j: int| 0 <= j < d.len() implies super::independent::w3c_ascii_fold(#[trigger] d[j]) == doctype_lower()[j] by {}
    assert forall|j: int| 0 <= j < p.len() implies super::independent::w3c_ascii_fold(#[trigger] p[j]) == public_lower()[j] by {}
    assert forall|j: int| 0 <= j < s.len() implies super::independent::w3c_ascii_fold(#[trigger] s[j]) == system_lower()[j] by {}
    lemma_word_at_ci(input, pos, d, doctype_lower());
    lemma_word_at_ci(input, pos, p, public_lower());
    lemma_word_at_ci(input, pos, s, system_lower());
    lemma_word_at(input, pos, seq![0x002Du32, 0x002Du32]);
    assert(super::independent::w3c_word_cdata() =~= cdata_open());
    lemma_word_at(input, pos, cdata_open());
}

/// The W3C helpers that compute what the living standard's helpers do.
pub proof fn lemma_helpers()
    ensures
        forall|a: Seq<u32>, b: Seq<u32>| #[trigger] super::independent::w3c_same(a, b) == (a == b),
        forall|a: Seq<Attribute>, n: Seq<u32>| #[trigger] super::independent::w3c_name_taken(a, n, 0)
            == has_attribute_named(a, n),
        forall|s: Seq<u32>| #[trigger] super::independent::w3c_characters(s) == chars(s),
{
    assert forall|a: Seq<u32>, b: Seq<u32>| #[trigger] super::independent::w3c_same(a, b) == (a == b) by {
        lemma_same(a, b);
    }
    assert forall|a: Seq<Attribute>, n: Seq<u32>| #[trigger] super::independent::w3c_name_taken(a, n, 0)
        == has_attribute_named(a, n) by {
        lemma_name_taken(a, n);
    }
    assert forall|s: Seq<u32>| #[trigger] super::independent::w3c_characters(s) == chars(s) by {
        assert(super::independent::w3c_characters(s) =~= chars(s));
    }
}

proof fn lemma_same(a: Seq<u32>, b: Seq<u32>)
    ensures
        super::independent::w3c_same(a, b) == (a == b),
{
    lemma_match_word(a, 0, b, 0);
    if a.len() == b.len() && super::independent::w3c_same(a, b) {
        assert(a =~= b);
    }
}

proof fn lemma_name_taken_from(a: Seq<Attribute>, n: Seq<u32>, k: nat)
    requires
        k <= a.len(),
    ensures
        super::independent::w3c_name_taken(a, n, k) == has_attribute_named(a.subrange(k as int, a.len() as int), n),
    decreases a.len() - k,
{
    lemma_helpers_same_only();
    if k < a.len() {
        lemma_name_taken_from(a, n, k + 1);
        lemma_has_named_cons(a.subrange(k as int, a.len() as int), n);
        assert(a.subrange(k as int, a.len() as int).subrange(1, (a.len() - k) as int) =~= a.subrange((k + 1) as int, a.len() as int));
    } else {
        assert(a.subrange(k as int, a.len() as int) =~= Seq::<Attribute>::empty());
    }
}

proof fn lemma_helpers_same_only()
    ensures
        forall|a: Seq<u32>, b: Seq<u32>| #[trigger] super::independent::w3c_same(a, b) == (a == b),
{
    assert forall|a: Seq<u32>, b: Seq<u32>| #[trigger] super::independent::w3c_same(a, b) == (a == b) by {
        lemma_same(a, b);
    }
}

/// [`has_attribute_named`] (which looks from the end) of a non-empty list is
/// its first name or the rest's.
proof fn lemma_has_named_cons(a: Seq<Attribute>, n: Seq<u32>)
    requires
        a.len() > 0,
    ensures
        has_attribute_named(a, n) == (a[0].name == n || has_attribute_named(a.subrange(1, a.len() as int), n)),
    decreases a.len(),
{
    if a.len() > 1 {
        lemma_has_named_cons(a.drop_last(), n);
        assert(a.drop_last().subrange(1, (a.len() - 1) as int) =~= a.subrange(1, a.len() as int).drop_last());
        assert(a.subrange(1, a.len() as int).last() == a.last());
    } else {
        assert(a.subrange(1, a.len() as int) =~= Seq::<Attribute>::empty());
        assert(a.drop_last() =~= Seq::<Attribute>::empty());
    }
}

proof fn lemma_name_taken(a: Seq<Attribute>, n: Seq<u32>)
    ensures
        super::independent::w3c_name_taken(a, n, 0) == has_attribute_named(a, n),
{
    lemma_name_taken_from(a, n, 0);
    assert(a.subrange(0, a.len() as int) =~= a);
}

proof fn lemma_eq_data_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Data,
    ensures
        step_related(input, data_state(input, t), super::independent::w3c_data(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rcdata_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Rcdata,
    ensures
        step_related(input, rcdata_state(input, t), super::independent::w3c_rcdata(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rawtext_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Rawtext,
    ensures
        step_related(input, rawtext_state(input, t), super::independent::w3c_rawtext(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptData,
    ensures
        step_related(input, script_data_state(input, t), super::independent::w3c_script_data(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_plaintext_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Plaintext,
    ensures
        step_related(input, plaintext_state(input, t), super::independent::w3c_plaintext(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is TagOpen,
    ensures
        step_related(input, tag_open_state(input, t), super::independent::w3c_tag_open(input, w)) || (!super::independent::w3c_stopped(input, super::independent::w3c_tag_open(input, w).0)
            && super::independent::w3c_tag_open(input, w).0.state == super::independent::W3cState::Data
            && after_ok(input, tag_open_state(input, t), super::independent::w3c_tag_open(input, w).1 + super::independent::w3c_data(input, super::independent::w3c_tag_open(input, w).0).1, super::independent::w3c_data(input, super::independent::w3c_tag_open(input, w).0).0)),
{
    lemma_helpers();
    if t.pos < input.len() {
        assert(input[t.pos - 1] == 0x3C);
        assert(input[t.pos as int] != 0x3F);
    } else {
        assert(seq![ch(0x3C)] + Seq::<Token>::empty().push(Token::EndOfFile) =~= seq![ch(0x3C)].push(
            Token::EndOfFile,
        ));
        assert(seq![Token::Character(0x003C)] =~= seq![ch(0x3C)]);
    }
}

proof fn lemma_eq_end_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is EndTagOpen,
    ensures
        step_related(input, end_tag_open_state(input, t), super::independent::w3c_end_tag_open(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_tag_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is TagName,
    ensures
        step_related(input, tag_name_state(input, t), super::independent::w3c_tag_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rcdata_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RcdataLessThanSign,
    ensures
        step_related(input, rcdata_less_than_sign_state(input, t), super::independent::w3c_rcdata_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rcdata_end_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RcdataEndTagOpen,
    ensures
        step_related(input, rcdata_end_tag_open_state(input, t), super::independent::w3c_rcdata_end_tag_open(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rcdata_end_tag_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RcdataEndTagName,
    ensures
        step_related(input, rcdata_end_tag_name_state(input, t), super::independent::w3c_rcdata_end_tag_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rawtext_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RawtextLessThanSign,
    ensures
        step_related(input, rawtext_less_than_sign_state(input, t), super::independent::w3c_rawtext_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rawtext_end_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RawtextEndTagOpen,
    ensures
        step_related(input, rawtext_end_tag_open_state(input, t), super::independent::w3c_rawtext_end_tag_open(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_rawtext_end_tag_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is RawtextEndTagName,
    ensures
        step_related(input, rawtext_end_tag_name_state(input, t), super::independent::w3c_rawtext_end_tag_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataLessThanSign,
    ensures
        step_related(input, script_data_less_than_sign_state(input, t), super::independent::w3c_script_data_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_end_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEndTagOpen,
    ensures
        step_related(input, script_data_end_tag_open_state(input, t), super::independent::w3c_script_data_end_tag_open(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_end_tag_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEndTagName,
    ensures
        step_related(input, script_data_end_tag_name_state(input, t), super::independent::w3c_script_data_end_tag_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escape_start_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapeStart,
    ensures
        step_related(input, script_data_escape_start_state(input, t), super::independent::w3c_script_data_escape_start(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escape_start_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapeStartDash,
    ensures
        step_related(input, script_data_escape_start_dash_state(input, t), super::independent::w3c_script_data_escape_start_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscaped,
    ensures
        step_related(input, script_data_escaped_state(input, t), super::independent::w3c_script_data_escaped(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapedDash,
    ensures
        step_related(input, script_data_escaped_dash_state(input, t), super::independent::w3c_script_data_escaped_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapedDashDash,
    ensures
        step_related(input, script_data_escaped_dash_dash_state(input, t), super::independent::w3c_script_data_escaped_dash_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapedLessThanSign,
    ensures
        step_related(input, script_data_escaped_less_than_sign_state(input, t), super::independent::w3c_script_data_escaped_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_end_tag_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapedEndTagOpen,
    ensures
        step_related(input, script_data_escaped_end_tag_open_state(input, t), super::independent::w3c_script_data_escaped_end_tag_open(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_escaped_end_tag_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataEscapedEndTagName,
    ensures
        step_related(input, script_data_escaped_end_tag_name_state(input, t), super::independent::w3c_script_data_escaped_end_tag_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escape_start_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapeStart,
    ensures
        step_related(input, script_data_double_escape_start_state(input, t), super::independent::w3c_script_data_double_escape_start(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escaped_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscaped,
    ensures
        step_related(input, script_data_double_escaped_state(input, t), super::independent::w3c_script_data_double_escaped(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escaped_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedDash,
    ensures
        step_related(input, script_data_double_escaped_dash_state(input, t), super::independent::w3c_script_data_double_escaped_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedDashDash,
    ensures
        step_related(input, script_data_double_escaped_dash_dash_state(input, t), super::independent::w3c_script_data_double_escaped_dash_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapedLessThanSign,
    ensures
        step_related(input, script_data_double_escaped_less_than_sign_state(input, t), super::independent::w3c_script_data_double_escaped_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_script_data_double_escape_end_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is ScriptDataDoubleEscapeEnd,
    ensures
        step_related(input, script_data_double_escape_end_state(input, t), super::independent::w3c_script_data_double_escape_end(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_before_attribute_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BeforeAttributeName,
    ensures
        step_related(input, before_attribute_name_state(input, t), super::independent::w3c_before_attribute_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_attribute_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AttributeName,
    ensures
        step_related(input, attribute_name_state(input, t), super::independent::w3c_attribute_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_after_attribute_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterAttributeName,
    ensures
        step_related(input, after_attribute_name_state(input, t), super::independent::w3c_after_attribute_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_before_attribute_value_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BeforeAttributeValue,
    ensures
        step_related(input, before_attribute_value_state(input, t), super::independent::w3c_before_attribute_value(input, w)) || (!super::independent::w3c_stopped(input, super::independent::w3c_before_attribute_value(input, w).0)
            && super::independent::w3c_before_attribute_value(input, w).0.state == super::independent::W3cState::AttributeValueUnquoted
            && after_ok(input, before_attribute_value_state(input, t), super::independent::w3c_before_attribute_value(input, w).1 + super::independent::w3c_attribute_value_unquoted(input, super::independent::w3c_before_attribute_value(input, w).0).1, super::independent::w3c_attribute_value_unquoted(input, super::independent::w3c_before_attribute_value(input, w).0).0)),
{
    lemma_helpers();
}

proof fn lemma_eq_attribute_value_double_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AttributeValueDoubleQuoted,
    ensures
        step_related(input, attribute_value_double_quoted_state(input, t), super::independent::w3c_attribute_value_double_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_attribute_value_single_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AttributeValueSingleQuoted,
    ensures
        step_related(input, attribute_value_single_quoted_state(input, t), super::independent::w3c_attribute_value_single_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_attribute_value_unquoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AttributeValueUnquoted,
    ensures
        step_related(input, attribute_value_unquoted_state(input, t), super::independent::w3c_attribute_value_unquoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_after_attribute_value_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterAttributeValueQuoted,
    ensures
        step_related(input, after_attribute_value_quoted_state(input, t), super::independent::w3c_after_attribute_value_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_self_closing_start_tag_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is SelfClosingStartTag,
    ensures
        step_related(input, self_closing_start_tag_state(input, t), super::independent::w3c_self_closing_start_tag(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_bogus_comment_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BogusComment,
    ensures
        step_related(input, bogus_comment_state(input, t), super::independent::w3c_bogus_comment(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_markup_declaration_open_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is MarkupDeclarationOpen,
    ensures
        step_related(input, markup_declaration_open_state(input, t), super::independent::w3c_markup_declaration_open(input, w)),
{
    lemma_helpers();
    lemma_words(input, t.pos);
    assert(!starts_with(input, t.pos, cdata_open()));
}

proof fn lemma_eq_comment_start_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentStart,
    ensures
        step_related(input, comment_start_state(input, t), super::independent::w3c_comment_start(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_start_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentStartDash,
    ensures
        step_related(input, comment_start_dash_state(input, t), super::independent::w3c_comment_start_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Comment,
    ensures
        step_related(input, comment_state(input, t), super::independent::w3c_comment(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_less_than_sign_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentLessThanSign,
    ensures
        step_related(input, comment_less_than_sign_state(input, t), super::independent::w3c_comment_less_than_sign(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_less_than_sign_bang_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentLessThanSignBang,
    ensures
        step_related(input, comment_less_than_sign_bang_state(input, t), super::independent::w3c_comment_less_than_sign_bang(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_less_than_sign_bang_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentLessThanSignBangDash,
    ensures
        step_related(input, comment_less_than_sign_bang_dash_state(input, t), super::independent::w3c_comment_less_than_sign_bang_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_less_than_sign_bang_dash_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentLessThanSignBangDashDash,
    ensures
        step_related(input, comment_less_than_sign_bang_dash_dash_state(input, t), super::independent::w3c_comment_less_than_sign_bang_dash_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_end_dash_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentEndDash,
    ensures
        step_related(input, comment_end_dash_state(input, t), super::independent::w3c_comment_end_dash(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_end_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentEnd,
    ensures
        step_related(input, comment_end_state(input, t), super::independent::w3c_comment_end(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_comment_end_bang_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CommentEndBang,
    ensures
        step_related(input, comment_end_bang_state(input, t), super::independent::w3c_comment_end_bang(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is Doctype,
    ensures
        step_related(input, doctype_state(input, t), super::independent::w3c_doctype(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_before_doctype_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BeforeDoctypeName,
    ensures
        step_related(input, before_doctype_name_state(input, t), super::independent::w3c_before_doctype_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is DoctypeName,
    ensures
        step_related(input, doctype_name_state(input, t), super::independent::w3c_doctype_name(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_after_doctype_name_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterDoctypeName,
    ensures
        step_related(input, after_doctype_name_state(input, t), super::independent::w3c_after_doctype_name(input, w)) || (after_doctype_name_state(input, t).1.len() == 0 && after_doctype_name_state(input, t).0.state is BogusDoctype
            && !stopped(input, after_doctype_name_state(input, t).0) && step_related(input, bogus_doctype_state(input, after_doctype_name_state(input, t).0), super::independent::w3c_after_doctype_name(input, w))),
{
    lemma_helpers();
    lemma_words(input, t.pos);
    assert(!starts_with(input, t.pos, cdata_open()));
}

proof fn lemma_eq_after_doctype_public_keyword_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterDoctypePublicKeyword,
    ensures
        step_related(input, after_doctype_public_keyword_state(input, t), super::independent::w3c_after_doctype_public_keyword(input, w)) || (after_doctype_public_keyword_state(input, t).1.len() == 0 && after_doctype_public_keyword_state(input, t).0.state is BogusDoctype
            && !stopped(input, after_doctype_public_keyword_state(input, t).0) && step_related(input, bogus_doctype_state(input, after_doctype_public_keyword_state(input, t).0), super::independent::w3c_after_doctype_public_keyword(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_before_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BeforeDoctypePublicIdentifier,
    ensures
        step_related(input, before_doctype_public_identifier_state(input, t), super::independent::w3c_before_doctype_public_identifier(input, w)) || (before_doctype_public_identifier_state(input, t).1.len() == 0 && before_doctype_public_identifier_state(input, t).0.state is BogusDoctype
            && !stopped(input, before_doctype_public_identifier_state(input, t).0) && step_related(input, bogus_doctype_state(input, before_doctype_public_identifier_state(input, t).0), super::independent::w3c_before_doctype_public_identifier(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_public_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is DoctypePublicIdentifierDoubleQuoted,
    ensures
        step_related(input, doctype_public_identifier_double_quoted_state(input, t), super::independent::w3c_doctype_public_identifier_double_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_public_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is DoctypePublicIdentifierSingleQuoted,
    ensures
        step_related(input, doctype_public_identifier_single_quoted_state(input, t), super::independent::w3c_doctype_public_identifier_single_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_after_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterDoctypePublicIdentifier,
    ensures
        step_related(input, after_doctype_public_identifier_state(input, t), super::independent::w3c_after_doctype_public_identifier(input, w)) || (after_doctype_public_identifier_state(input, t).1.len() == 0 && after_doctype_public_identifier_state(input, t).0.state is BogusDoctype
            && !stopped(input, after_doctype_public_identifier_state(input, t).0) && step_related(input, bogus_doctype_state(input, after_doctype_public_identifier_state(input, t).0), super::independent::w3c_after_doctype_public_identifier(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_between_doctype_public_and_system_identifiers_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BetweenDoctypePublicAndSystemIdentifiers,
    ensures
        step_related(input, between_doctype_public_and_system_identifiers_state(input, t), super::independent::w3c_between_doctype_public_and_system_identifiers(input, w)) || (between_doctype_public_and_system_identifiers_state(input, t).1.len() == 0 && between_doctype_public_and_system_identifiers_state(input, t).0.state is BogusDoctype
            && !stopped(input, between_doctype_public_and_system_identifiers_state(input, t).0) && step_related(input, bogus_doctype_state(input, between_doctype_public_and_system_identifiers_state(input, t).0), super::independent::w3c_between_doctype_public_and_system_identifiers(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_after_doctype_system_keyword_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterDoctypeSystemKeyword,
    ensures
        step_related(input, after_doctype_system_keyword_state(input, t), super::independent::w3c_after_doctype_system_keyword(input, w)) || (after_doctype_system_keyword_state(input, t).1.len() == 0 && after_doctype_system_keyword_state(input, t).0.state is BogusDoctype
            && !stopped(input, after_doctype_system_keyword_state(input, t).0) && step_related(input, bogus_doctype_state(input, after_doctype_system_keyword_state(input, t).0), super::independent::w3c_after_doctype_system_keyword(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_before_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BeforeDoctypeSystemIdentifier,
    ensures
        step_related(input, before_doctype_system_identifier_state(input, t), super::independent::w3c_before_doctype_system_identifier(input, w)) || (before_doctype_system_identifier_state(input, t).1.len() == 0 && before_doctype_system_identifier_state(input, t).0.state is BogusDoctype
            && !stopped(input, before_doctype_system_identifier_state(input, t).0) && step_related(input, bogus_doctype_state(input, before_doctype_system_identifier_state(input, t).0), super::independent::w3c_before_doctype_system_identifier(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_system_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is DoctypeSystemIdentifierDoubleQuoted,
    ensures
        step_related(input, doctype_system_identifier_double_quoted_state(input, t), super::independent::w3c_doctype_system_identifier_double_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_doctype_system_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is DoctypeSystemIdentifierSingleQuoted,
    ensures
        step_related(input, doctype_system_identifier_single_quoted_state(input, t), super::independent::w3c_doctype_system_identifier_single_quoted(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_after_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is AfterDoctypeSystemIdentifier,
    ensures
        step_related(input, after_doctype_system_identifier_state(input, t), super::independent::w3c_after_doctype_system_identifier(input, w)) || (after_doctype_system_identifier_state(input, t).1.len() == 0 && after_doctype_system_identifier_state(input, t).0.state is BogusDoctype
            && !stopped(input, after_doctype_system_identifier_state(input, t).0) && step_related(input, bogus_doctype_state(input, after_doctype_system_identifier_state(input, t).0), super::independent::w3c_after_doctype_system_identifier(input, w))),
{
    lemma_helpers();
}

proof fn lemma_eq_bogus_doctype_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is BogusDoctype,
    ensures
        step_related(input, bogus_doctype_state(input, t), super::independent::w3c_bogus_doctype(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_cdata_section_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CdataSection,
    ensures
        step_related(input, cdata_section_state(input, t), super::independent::w3c_cdata_section(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_cdata_section_bracket_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CdataSectionBracket,
    ensures
        step_related(input, cdata_section_bracket_state(input, t), super::independent::w3c_cdata_section_bracket(input, w)),
{
    lemma_helpers();
}

proof fn lemma_eq_cdata_section_end_state(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
        t.state is CdataSectionEnd,
    ensures
        step_related(input, cdata_section_end_state(input, t), super::independent::w3c_cdata_section_end(input, w)),
{
    lemma_helpers();
}

/// One step of each, on related tokenizers.
#[verifier::rlimit(400)]
pub proof fn lemma_step_related(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
        !stopped(input, t),
    ensures
        corresponds(input, t, w),
{
    reveal(step);
    reveal(super::independent::w3c_step);
    match t.state {
            State::Data => lemma_eq_data_state(input, t, w),
            State::Rcdata => lemma_eq_rcdata_state(input, t, w),
            State::Rawtext => lemma_eq_rawtext_state(input, t, w),
            State::ScriptData => lemma_eq_script_data_state(input, t, w),
            State::Plaintext => lemma_eq_plaintext_state(input, t, w),
            State::TagOpen => lemma_eq_tag_open_state(input, t, w),
            State::EndTagOpen => lemma_eq_end_tag_open_state(input, t, w),
            State::TagName => lemma_eq_tag_name_state(input, t, w),
            State::RcdataLessThanSign => lemma_eq_rcdata_less_than_sign_state(input, t, w),
            State::RcdataEndTagOpen => lemma_eq_rcdata_end_tag_open_state(input, t, w),
            State::RcdataEndTagName => lemma_eq_rcdata_end_tag_name_state(input, t, w),
            State::RawtextLessThanSign => lemma_eq_rawtext_less_than_sign_state(input, t, w),
            State::RawtextEndTagOpen => lemma_eq_rawtext_end_tag_open_state(input, t, w),
            State::RawtextEndTagName => lemma_eq_rawtext_end_tag_name_state(input, t, w),
            State::ScriptDataLessThanSign => lemma_eq_script_data_less_than_sign_state(input, t, w),
            State::ScriptDataEndTagOpen => lemma_eq_script_data_end_tag_open_state(input, t, w),
            State::ScriptDataEndTagName => lemma_eq_script_data_end_tag_name_state(input, t, w),
            State::ScriptDataEscapeStart => lemma_eq_script_data_escape_start_state(input, t, w),
            State::ScriptDataEscapeStartDash => lemma_eq_script_data_escape_start_dash_state(input, t, w),
            State::ScriptDataEscaped => lemma_eq_script_data_escaped_state(input, t, w),
            State::ScriptDataEscapedDash => lemma_eq_script_data_escaped_dash_state(input, t, w),
            State::ScriptDataEscapedDashDash => lemma_eq_script_data_escaped_dash_dash_state(input, t, w),
            State::ScriptDataEscapedLessThanSign => lemma_eq_script_data_escaped_less_than_sign_state(input, t, w),
            State::ScriptDataEscapedEndTagOpen => lemma_eq_script_data_escaped_end_tag_open_state(input, t, w),
            State::ScriptDataEscapedEndTagName => lemma_eq_script_data_escaped_end_tag_name_state(input, t, w),
            State::ScriptDataDoubleEscapeStart => lemma_eq_script_data_double_escape_start_state(input, t, w),
            State::ScriptDataDoubleEscaped => lemma_eq_script_data_double_escaped_state(input, t, w),
            State::ScriptDataDoubleEscapedDash => lemma_eq_script_data_double_escaped_dash_state(input, t, w),
            State::ScriptDataDoubleEscapedDashDash => lemma_eq_script_data_double_escaped_dash_dash_state(input, t, w),
            State::ScriptDataDoubleEscapedLessThanSign => lemma_eq_script_data_double_escaped_less_than_sign_state(input, t, w),
            State::ScriptDataDoubleEscapeEnd => lemma_eq_script_data_double_escape_end_state(input, t, w),
            State::BeforeAttributeName => lemma_eq_before_attribute_name_state(input, t, w),
            State::AttributeName => lemma_eq_attribute_name_state(input, t, w),
            State::AfterAttributeName => lemma_eq_after_attribute_name_state(input, t, w),
            State::BeforeAttributeValue => lemma_eq_before_attribute_value_state(input, t, w),
            State::AttributeValueDoubleQuoted => lemma_eq_attribute_value_double_quoted_state(input, t, w),
            State::AttributeValueSingleQuoted => lemma_eq_attribute_value_single_quoted_state(input, t, w),
            State::AttributeValueUnquoted => lemma_eq_attribute_value_unquoted_state(input, t, w),
            State::AfterAttributeValueQuoted => lemma_eq_after_attribute_value_quoted_state(input, t, w),
            State::SelfClosingStartTag => lemma_eq_self_closing_start_tag_state(input, t, w),
            State::BogusComment => lemma_eq_bogus_comment_state(input, t, w),
            State::MarkupDeclarationOpen => lemma_eq_markup_declaration_open_state(input, t, w),
            State::CommentStart => lemma_eq_comment_start_state(input, t, w),
            State::CommentStartDash => lemma_eq_comment_start_dash_state(input, t, w),
            State::Comment => lemma_eq_comment_state(input, t, w),
            State::CommentLessThanSign => lemma_eq_comment_less_than_sign_state(input, t, w),
            State::CommentLessThanSignBang => lemma_eq_comment_less_than_sign_bang_state(input, t, w),
            State::CommentLessThanSignBangDash => lemma_eq_comment_less_than_sign_bang_dash_state(input, t, w),
            State::CommentLessThanSignBangDashDash => lemma_eq_comment_less_than_sign_bang_dash_dash_state(input, t, w),
            State::CommentEndDash => lemma_eq_comment_end_dash_state(input, t, w),
            State::CommentEnd => lemma_eq_comment_end_state(input, t, w),
            State::CommentEndBang => lemma_eq_comment_end_bang_state(input, t, w),
            State::Doctype => lemma_eq_doctype_state(input, t, w),
            State::BeforeDoctypeName => lemma_eq_before_doctype_name_state(input, t, w),
            State::DoctypeName => lemma_eq_doctype_name_state(input, t, w),
            State::AfterDoctypeName => lemma_eq_after_doctype_name_state(input, t, w),
            State::AfterDoctypePublicKeyword => lemma_eq_after_doctype_public_keyword_state(input, t, w),
            State::BeforeDoctypePublicIdentifier => lemma_eq_before_doctype_public_identifier_state(input, t, w),
            State::DoctypePublicIdentifierDoubleQuoted => lemma_eq_doctype_public_identifier_double_quoted_state(input, t, w),
            State::DoctypePublicIdentifierSingleQuoted => lemma_eq_doctype_public_identifier_single_quoted_state(input, t, w),
            State::AfterDoctypePublicIdentifier => lemma_eq_after_doctype_public_identifier_state(input, t, w),
            State::BetweenDoctypePublicAndSystemIdentifiers => lemma_eq_between_doctype_public_and_system_identifiers_state(input, t, w),
            State::AfterDoctypeSystemKeyword => lemma_eq_after_doctype_system_keyword_state(input, t, w),
            State::BeforeDoctypeSystemIdentifier => lemma_eq_before_doctype_system_identifier_state(input, t, w),
            State::DoctypeSystemIdentifierDoubleQuoted => lemma_eq_doctype_system_identifier_double_quoted_state(input, t, w),
            State::DoctypeSystemIdentifierSingleQuoted => lemma_eq_doctype_system_identifier_single_quoted_state(input, t, w),
            State::AfterDoctypeSystemIdentifier => lemma_eq_after_doctype_system_identifier_state(input, t, w),
            State::BogusDoctype => lemma_eq_bogus_doctype_state(input, t, w),
            State::CdataSection => lemma_eq_cdata_section_state(input, t, w),
            State::CdataSectionBracket => lemma_eq_cdata_section_bracket_state(input, t, w),
            State::CdataSectionEnd => lemma_eq_cdata_section_end_state(input, t, w),
        _ => {},
    }
}

/// Related tokenizers on an input of the domain emit the same tokens.
pub proof fn lemma_runs_equal(input: Seq<u32>, t: Tokenizer, w: super::independent::W3cTokenizer)
    requires
        in_domain(input),
        inv_eq(input, t),
        related(w, t),
    ensures
        super::independent::w3c_run(input, w) == run(input, t),
    decreases super::termination::remaining(input, t), super::termination::rank(input, t),
{
    if !stopped(input, t) {
        super::termination::lemma_step_decreases(input, t);
        lemma_step_related(input, t, w);
        let (n, toks) = step(input, t);
        let ws = super::independent::w3c_step(input, w);
        if step_related(input, step(input, t), ws) {
            if !stopped(input, n) {
                lemma_runs_equal(input, n, ws.0);
            }
        } else if toks.len() == 0 && !stopped(input, n) && step_related(input, step(input, n), ws) {
            super::termination::lemma_step_decreases(input, n);
            let (n2, toks2) = step(input, n);
            assert(run(input, t) == toks + run(input, n));
            assert(toks + run(input, n) =~= run(input, n));
            if !stopped(input, n2) {
                lemma_runs_equal(input, n2, ws.0);
            }
        } else {
            let ws2 = super::independent::w3c_step(input, ws.0);
            assert(super::independent::w3c_run(input, w) == ws.1 + super::independent::w3c_run(input, ws.0));
            if !stopped(input, n) {
                lemma_runs_equal(input, n, ws2.0);
                assert(ws.1 + (ws2.1 + super::independent::w3c_run(input, ws2.0)) =~= (ws.1 + ws2.1)
                    + super::independent::w3c_run(input, ws2.0));
            } else {
                assert(ws.1 + ws2.1 == toks);
            }
        }
    }
}

/// `theorem_w3c_equivalent`: on every input of the domain, from the
/// start states the html5lib tests use, the W3C HTML 5.2 transcription and
/// the living standard's give the same tokens.
pub proof fn theorem_w3c_equivalent(input: Seq<u32>, start_state: State, last_start_tag: Option<Seq<u32>>)
    requires
        in_domain(input),
        start_state is Data || start_state is Rcdata || start_state is Rawtext || start_state is ScriptData
            || start_state is Plaintext || start_state is CdataSection,
    ensures
        super::independent::w3c_tokenize(input, w3c_state(start_state).unwrap(), last_start_tag) == tokenize(
            input,
            start_state,
            last_start_tag,
        ),
{
    lemma_runs_equal(
        input,
        initial(start_state, last_start_tag),
        super::independent::w3c_initial(w3c_state(start_state).unwrap(), last_start_tag),
    );
}

} // verus!
