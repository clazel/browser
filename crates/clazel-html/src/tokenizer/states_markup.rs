//! The executable states §13.2.5.32 to §13.2.5.68 (attributes, comments,
//! DOCTYPE), each proven equal to its spec function. The step comments
//! live in [`super::spec`].

use super::actions::*;
use super::buffer::*;
#[allow(unused_imports)]
use super::spec::*;
use super::states_text::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A string of one code point.
fn one_char(c: u32) -> (r: Vec<u32>)
    ensures
        r@ == seq![c],
{
    let r = from_slice([c].as_slice());
    assert(r@ =~= seq![c]);
    r
}

/// §13.2.5.32 Before attribute name state.
pub fn before_attribute_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_attribute_name_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        None => {
            t.state = State::AfterAttributeName;
        },
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            } else if c == 0x2F || c == 0x3E {
                t.state = State::AfterAttributeName;
            } else if c == 0x3D {
                consume(input, t);
                start_attribute_exec(t, one_char(c), Ghost(consumed(st)));
                t.state = State::AttributeName;
            } else {
                start_attribute_exec(t, Vec::new(), Ghost(st));
                t.state = State::AttributeName;
            }
        },
    }
}

/// §13.2.5.33 Attribute name state.
pub fn attribute_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(attribute_name_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        None => {
            leave_attribute_name_exec(t, Ghost(st));
            t.state = State::AfterAttributeName;
        },
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) || c == 0x2F || c == 0x3E {
                leave_attribute_name_exec(t, Ghost(st));
                t.state = State::AfterAttributeName;
            } else if c == 0x3D {
                consume(input, t);
                leave_attribute_name_exec(t, Ghost(consumed(st)));
                t.state = State::BeforeAttributeValue;
            } else if is_upper_exec(c) {
                consume(input, t);
                // Never overflows: c is at most 0x5A.
                append_to_attribute_name_exec(t, c.saturating_add(0x20), Ghost(consumed(st)));
            } else if c == 0x00 {
                consume(input, t);
                append_to_attribute_name_exec(t, 0xFFFD, Ghost(consumed(st)));
            } else {
                consume(input, t);
                append_to_attribute_name_exec(t, c, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.34 After attribute name state.
pub fn after_attribute_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_attribute_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            } else if c == 0x2F {
                consume(input, t);
                t.state = State::SelfClosingStartTag;
            } else if c == 0x3D {
                consume(input, t);
                t.state = State::BeforeAttributeValue;
            } else if c == 0x3E {
                consume(input, t);
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else {
                start_attribute_exec(t, Vec::new(), Ghost(st));
                t.state = State::AttributeName;
            }
        },
    }
}

/// §13.2.5.35 Before attribute value state.
pub fn before_attribute_value_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_attribute_value_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_tab_lf_ff_space_exec(c) => {
            consume(input, t);
        },
        Some(0x22) => {
            consume(input, t);
            t.state = State::AttributeValueDoubleQuoted;
        },
        Some(0x27) => {
            consume(input, t);
            t.state = State::AttributeValueSingleQuoted;
        },
        Some(0x3E) => {
            consume(input, t);
            t.state = State::Data;
            emit_current_tag_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
        },
        _ => {
            t.state = State::AttributeValueUnquoted;
        },
    }
}

/// The quoted attribute value states.
fn attribute_value_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    quote: u32,
    ret: ReturnState,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(attribute_value_quoted_state(input@, st, quote, ret), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if c == quote {
                t.state = State::AfterAttributeValueQuoted;
            } else if c == 0x26 {
                t.return_state = ret;
                t.state = State::CharacterReference;
            } else if c == 0x00 {
                append_to_attribute_value_exec(t, 0xFFFD, Ghost(consumed(st)));
            } else {
                append_to_attribute_value_exec(t, c, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.36 Attribute value (double-quoted) state.
pub fn attribute_value_double_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(attribute_value_double_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    attribute_value_quoted_state_exec(input, t, out, 0x22, ReturnState::AttributeValueDoubleQuoted, Ghost(st));
}

/// §13.2.5.37 Attribute value (single-quoted) state.
pub fn attribute_value_single_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(attribute_value_single_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    attribute_value_quoted_state_exec(input, t, out, 0x27, ReturnState::AttributeValueSingleQuoted, Ghost(st));
}

/// §13.2.5.38 Attribute value (unquoted) state.
pub fn attribute_value_unquoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(attribute_value_unquoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if is_tab_lf_ff_space_exec(c) {
                t.state = State::BeforeAttributeName;
            } else if c == 0x26 {
                t.return_state = ReturnState::AttributeValueUnquoted;
                t.state = State::CharacterReference;
            } else if c == 0x3E {
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else if c == 0x00 {
                append_to_attribute_value_exec(t, 0xFFFD, Ghost(consumed(st)));
            } else {
                append_to_attribute_value_exec(t, c, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.39 After attribute value (quoted) state.
pub fn after_attribute_value_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_attribute_value_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
                t.state = State::BeforeAttributeName;
            } else if c == 0x2F {
                consume(input, t);
                t.state = State::SelfClosingStartTag;
            } else if c == 0x3E {
                consume(input, t);
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else {
                t.state = State::BeforeAttributeName;
            }
        },
    }
}

/// §13.2.5.40 Self-closing start tag state.
pub fn self_closing_start_tag_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(self_closing_start_tag_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            if c == 0x3E {
                consume(input, t);
                set_self_closing_exec(t, Ghost(consumed(st)));
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(set_self_closing(consumed(st)), State::Data)));
            } else {
                t.state = State::BeforeAttributeName;
            }
        },
    }
}

/// "Emit the current token. Emit an end-of-file token."
fn emit_current_and_eof(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        post(emit_eof(st, emit_current(st, seq![])), final(t)@, old(out)@, final(out)@),
{
    emit_current_exec(t, out, Ghost(st));
    t.done = true;
    push_token(out, ExecToken::EndOfFile);
    assert(emit_eof(st, emit_current(st, seq![])).1 =~= seq![st.current, Token::EndOfFile]);
}

/// Consume, "switch to the data state" and "emit the current token".
fn consume_switch_to_data_and_emit(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        super::contract::abstracts(st, old(t)@),
        st.pos < input@.len(),
    ensures
        post(
            (switch_to(consumed(st), State::Data), emit_current(consumed(st), seq![])),
            final(t)@,
            old(out)@,
            final(out)@,
        ),
{
    consume(input, t);
    t.state = State::Data;
    emit_current_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
}

/// §13.2.5.41 Bogus comment state.
pub fn bogus_comment_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(bogus_comment_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                consume(input, t);
                append_char_to_comment_exec(t, if c == 0x00 { 0xFFFD } else { c }, Ghost(consumed(st)));
            }
        },
    }
}

/// Whether the input from `pos` on starts with `s` (exactly).
fn starts_with_exec(input: &[u32], pos: usize, s: &[u32]) -> (r: bool)
    requires
        pos <= input.len(),
    ensures
        r == starts_with(input@, pos as nat, s@),
{
    // Never saturates: pos <= input.len().
    if s.len() > input.len().saturating_sub(pos) {
        return false;
    }
    let mut k: usize = 0;
    while k < s.len()
        invariant
            k <= s.len(),
            pos + s.len() <= input.len(),
            forall|j: int| 0 <= j < k ==> input@[pos + j] == s@[j],
        decreases s.len() - k,
    {
        // Never saturates: pos + k < input.len().
        if at32(input, pos.saturating_add(k)) != at32(s, k) {
            assert(input@.subrange(pos as int, pos + s.len())[k as int] != s@[k as int]);
            return false;
        }
        k = k.saturating_add(1);
    }
    assert(input@.subrange(pos as int, pos + s.len()) =~= s@);
    true
}

/// ASCII lowercase of one code point.
fn ascii_lower_exec(c: u32) -> (r: u32)
    ensures
        r == ascii_lower(c),
{
    if is_upper_exec(c) {
        // Never overflows: c is at most 0x5A.
        c.saturating_add(0x20)
    } else {
        c
    }
}

/// Whether the input from `pos` on starts with `s` ASCII
/// case-insensitively (`s` lowercase).
fn starts_with_ci_exec(input: &[u32], pos: usize, s: &[u32]) -> (r: bool)
    requires
        pos <= input.len(),
    ensures
        r == starts_with_ci(input@, pos as nat, s@),
{
    // Never saturates: pos <= input.len().
    if s.len() > input.len().saturating_sub(pos) {
        return false;
    }
    let ghost sub = input@.subrange(pos as int, pos + s.len()).map_values(|c: u32| ascii_lower(c));
    let mut k: usize = 0;
    while k < s.len()
        invariant
            k <= s.len(),
            pos + s.len() <= input.len(),
            sub == input@.subrange(pos as int, pos + s.len()).map_values(|c: u32| ascii_lower(c)),
            forall|j: int| 0 <= j < k ==> sub[j] == s@[j],
        decreases s.len() - k,
    {
        // Never saturates: pos + k < input.len().
        if ascii_lower_exec(at32(input, pos.saturating_add(k))) != at32(s, k) {
            assert(sub[k as int] != s@[k as int]);
            return false;
        }
        k = k.saturating_add(1);
    }
    assert(sub =~= s@);
    true
}

/// §13.2.5.42 Markup declaration open state.
pub fn markup_declaration_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(markup_declaration_open_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    let dashes: [u32; 2] = [0x2D, 0x2D];
    let doctype: [u32; 7] = [0x64, 0x6F, 0x63, 0x74, 0x79, 0x70, 0x65];
    let cdata: [u32; 7] = [0x5B, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B];
    assert(dashes@ =~= seq![0x2Du32, 0x2D]);
    assert(doctype@ =~= doctype_lower());
    assert(cdata@ =~= cdata_open());
    assert(dashes@.len() == 2 && doctype@.len() == 7 && cdata@.len() == 7);
    assert(input@.len() == input.len() as nat);
    if starts_with_exec(input, t.pos, dashes.as_slice()) {
        // Never saturates: two characters follow pos.
        t.pos = t.pos.saturating_add(2);
        assert(t.pos as nat == st.pos + 2);
        assert(super::contract::abstracts(Tokenizer { pos: st.pos + 2, ..st }, t@));
        new_comment_exec(t, Vec::new(), Ghost(Tokenizer { pos: st.pos + 2, ..st }));
        t.state = State::CommentStart;
    } else if starts_with_ci_exec(input, t.pos, doctype.as_slice()) {
        // Never saturates: seven characters follow pos.
        t.pos = t.pos.saturating_add(7);
        t.state = State::Doctype;
    } else if starts_with_exec(input, t.pos, cdata.as_slice()) {
        // Never saturates: seven characters follow pos.
        t.pos = t.pos.saturating_add(7);
        if t.in_foreign_content {
            t.state = State::CdataSection;
        } else {
            let data = from_slice([0x5Bu32, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B].as_slice());
            assert(data@ =~= cdata_open());
            new_comment_exec(t, data, Ghost(Tokenizer { pos: st.pos + 7, ..st }));
            t.state = State::BogusComment;
        }
    } else {
        new_comment_exec(t, Vec::new(), Ghost(st));
        t.state = State::BogusComment;
    }
}

/// §13.2.5.43 Comment start state.
pub fn comment_start_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_start_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x2D) => {
            consume(input, t);
            t.state = State::CommentStartDash;
        },
        Some(0x3E) => {
            consume_switch_to_data_and_emit(input, t, out, Ghost(st));
        },
        _ => {
            t.state = State::Comment;
        },
    }
}

/// §13.2.5.44 Comment start dash state.
pub fn comment_start_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_start_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x2D {
                consume(input, t);
                t.state = State::CommentEnd;
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                append_char_to_comment_exec(t, 0x2D, Ghost(st));
                t.state = State::Comment;
            }
        },
    }
}

/// §13.2.5.45 Comment state.
pub fn comment_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            consume(input, t);
            if c == 0x3C {
                append_char_to_comment_exec(t, c, Ghost(consumed(st)));
                t.state = State::CommentLessThanSign;
            } else if c == 0x2D {
                t.state = State::CommentEndDash;
            } else {
                append_char_to_comment_exec(t, if c == 0x00 { 0xFFFD } else { c }, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.46 Comment less-than sign state.
pub fn comment_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_less_than_sign_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c @ 0x21) => {
            consume(input, t);
            append_char_to_comment_exec(t, c, Ghost(consumed(st)));
            t.state = State::CommentLessThanSignBang;
        },
        Some(c @ 0x3C) => {
            consume(input, t);
            append_char_to_comment_exec(t, c, Ghost(consumed(st)));
        },
        _ => {
            t.state = State::Comment;
        },
    }
}

/// The comment less-than sign bang and bang dash states (§13.2.5.47 and
/// §13.2.5.48): on `-` consume and switch to `next`, else reconsume in
/// `otherwise`.
fn comment_bang_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    next: State,
    otherwise: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        super::contract::abstracts(
            match next_char(input@, st.pos) {
                Some(c) if c == 0x2D => switch_to(consumed(st), next),
                _ => switch_to(st, otherwise),
            },
            final(t)@,
        ),
{
    match next_char_exec(input, t.pos) {
        Some(0x2D) => {
            consume(input, t);
            t.state = next;
        },
        _ => {
            t.state = otherwise;
        },
    }
}

/// §13.2.5.47 Comment less-than sign bang state.
pub fn comment_less_than_sign_bang_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_less_than_sign_bang_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    comment_bang_exec(input, t, State::CommentLessThanSignBangDash, State::Comment, Ghost(st));
}

/// §13.2.5.48 Comment less-than sign bang dash state.
pub fn comment_less_than_sign_bang_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_less_than_sign_bang_dash_state(input@, st), final(t)@, old(_out)@, final(_out)@),
{
    comment_bang_exec(input, t, State::CommentLessThanSignBangDashDash, State::CommentEndDash, Ghost(st));
}

/// §13.2.5.49 Comment less-than sign bang dash dash state.
pub fn comment_less_than_sign_bang_dash_dash_state_exec(
    _input: &[u32],
    t: &mut ExecTokenizer,
    _out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(_input@, st, old(t)@),
    ensures
        post(comment_less_than_sign_bang_dash_dash_state(_input@, st), final(t)@, old(_out)@, final(_out)@),
{
    t.state = State::CommentEnd;
}

/// §13.2.5.50 Comment end dash state.
pub fn comment_end_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_end_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x2D {
                consume(input, t);
                t.state = State::CommentEnd;
            } else {
                append_char_to_comment_exec(t, 0x2D, Ghost(st));
                t.state = State::Comment;
            }
        },
    }
}

/// §13.2.5.51 Comment end state.
pub fn comment_end_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_end_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else if c == 0x21 {
                consume(input, t);
                t.state = State::CommentEndBang;
            } else if c == 0x2D {
                consume(input, t);
                append_char_to_comment_exec(t, 0x2D, Ghost(consumed(st)));
            } else {
                let two = from_slice([0x2Du32, 0x2D].as_slice());
                assert(two@ =~= seq![0x2Du32, 0x2D]);
                append_to_comment_exec(t, &two, Ghost(st));
                t.state = State::Comment;
            }
        },
    }
}

/// §13.2.5.52 Comment end bang state.
pub fn comment_end_bang_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(comment_end_bang_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    let dashes_bang = from_slice([0x2Du32, 0x2D, 0x21].as_slice());
    assert(dashes_bang@ =~= seq![0x2Du32, 0x2D, 0x21]);
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x2D {
                consume(input, t);
                append_to_comment_exec(t, &dashes_bang, Ghost(consumed(st)));
                t.state = State::CommentEndDash;
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                append_to_comment_exec(t, &dashes_bang, Ghost(st));
                t.state = State::Comment;
            }
        },
    }
}

/// "Create a new DOCTYPE token. Set its force-quirks flag to on. Emit the
/// current token. Emit an end-of-file token."
fn new_doctype_quirks_eof(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        post(
            emit_eof(
                set_force_quirks(new_doctype(st, None)),
                emit_current(set_force_quirks(new_doctype(st, None)), seq![]),
            ),
            final(t)@,
            old(out)@,
            final(out)@,
        ),
{
    new_doctype_exec(t, None, Ghost(st));
    set_force_quirks_exec(t, Ghost(new_doctype(st, None)));
    emit_current_and_eof(t, out, Ghost(set_force_quirks(new_doctype(st, None))));
}

/// "Set the current DOCTYPE token's force-quirks flag to on. Emit the
/// current DOCTYPE token. Emit an end-of-file token."
fn quirks_eof(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        post(emit_eof(set_force_quirks(st), emit_current(set_force_quirks(st), seq![])), final(t)@, old(out)@, final(out)@),
{
    set_force_quirks_exec(t, Ghost(st));
    emit_current_and_eof(t, out, Ghost(set_force_quirks(st)));
}

/// "Set the current DOCTYPE token's force-quirks flag to on. Switch to the
/// data state. Emit the current DOCTYPE token." after consuming.
fn consume_quirks_data_emit(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
        st.pos < input@.len(),
    ensures
        post(
            (
                switch_to(set_force_quirks(consumed(st)), State::Data),
                emit_current(switch_to(set_force_quirks(consumed(st)), State::Data), seq![]),
            ),
            final(t)@,
            old(out)@,
            final(out)@,
        ),
{
    consume(input, t);
    set_force_quirks_exec(t, Ghost(consumed(st)));
    t.state = State::Data;
    emit_current_exec(t, out, Ghost(switch_to(set_force_quirks(consumed(st)), State::Data)));
}

/// "Set the current DOCTYPE token's force-quirks flag to on. Reconsume in
/// the bogus DOCTYPE state."
fn quirks_bogus(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(switch_to(set_force_quirks(st), State::BogusDoctype), final(t)@),
{
    set_force_quirks_exec(t, Ghost(st));
    t.state = State::BogusDoctype;
}

/// §13.2.5.53 DOCTYPE state.
pub fn doctype_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => new_doctype_quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            }
            t.state = State::BeforeDoctypeName;
        },
    }
}

/// §13.2.5.54 Before DOCTYPE name state.
pub fn before_doctype_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_doctype_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => new_doctype_quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            consume(input, t);
            let ghost n = consumed(st);
            if is_tab_lf_ff_space_exec(c) {
            } else if c == 0x3E {
                new_doctype_exec(t, None, Ghost(n));
                set_force_quirks_exec(t, Ghost(new_doctype(n, None)));
                t.state = State::Data;
                emit_current_exec(t, out, Ghost(switch_to(set_force_quirks(new_doctype(n, None)), State::Data)));
            } else {
                let first = if is_upper_exec(c) {
                    // Never overflows: c is at most 0x5A.
                    c.saturating_add(0x20)
                } else if c == 0x00 {
                    0xFFFD
                } else {
                    c
                };
                new_doctype_exec(t, Some(one_char(first)), Ghost(n));
                t.state = State::DoctypeName;
            }
        },
    }
}

/// §13.2.5.55 DOCTYPE name state.
pub fn doctype_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
                t.state = State::AfterDoctypeName;
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                consume(input, t);
                let x = if is_upper_exec(c) {
                    // Never overflows: c is at most 0x5A.
                    c.saturating_add(0x20)
                } else if c == 0x00 {
                    0xFFFD
                } else {
                    c
                };
                append_to_doctype_name_exec(t, x, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.56 After DOCTYPE name state.
pub fn after_doctype_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    let public: [u32; 6] = [0x70, 0x75, 0x62, 0x6C, 0x69, 0x63];
    let system: [u32; 6] = [0x73, 0x79, 0x73, 0x74, 0x65, 0x6D];
    assert(public@ =~= public_lower());
    assert(system@ =~= system_lower());
    assert(public@.len() == 6 && system@.len() == 6);
    assert(input@.len() == input.len() as nat);
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else if starts_with_ci_exec(input, t.pos, public.as_slice()) {
                // Never saturates: six characters follow pos.
                t.pos = t.pos.saturating_add(6);
                assert(t.pos as nat == st.pos + 6);
                t.state = State::AfterDoctypePublicKeyword;
            } else if starts_with_ci_exec(input, t.pos, system.as_slice()) {
                // Never saturates: six characters follow pos.
                t.pos = t.pos.saturating_add(6);
                assert(t.pos as nat == st.pos + 6);
                t.state = State::AfterDoctypeSystemKeyword;
            } else {
                quirks_bogus(t, Ghost(st));
            }
        },
    }
}

/// The after DOCTYPE public and system keyword states.
fn after_doctype_keyword_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    public: bool,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_keyword_state(input@, st, public), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
                t.state = if public {
                    State::BeforeDoctypePublicIdentifier
                } else {
                    State::BeforeDoctypeSystemIdentifier
                };
            } else if c == 0x22 || c == 0x27 {
                consume(input, t);
                set_identifier_empty_exec(t, public, Ghost(consumed(st)));
                t.state = if public {
                    if c == 0x22 {
                        State::DoctypePublicIdentifierDoubleQuoted
                    } else {
                        State::DoctypePublicIdentifierSingleQuoted
                    }
                } else if c == 0x22 {
                    State::DoctypeSystemIdentifierDoubleQuoted
                } else {
                    State::DoctypeSystemIdentifierSingleQuoted
                };
            } else if c == 0x3E {
                consume_quirks_data_emit(input, t, out, Ghost(st));
            } else {
                quirks_bogus(t, Ghost(st));
            }
        },
    }
}

/// §13.2.5.57 After DOCTYPE public keyword state.
pub fn after_doctype_public_keyword_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_public_keyword_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    after_doctype_keyword_state_exec(input, t, out, true, Ghost(st));
}

/// The before DOCTYPE public and system identifier states.
fn before_doctype_identifier_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    public: bool,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_doctype_identifier_state(input@, st, public), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            } else if c == 0x22 || c == 0x27 {
                consume(input, t);
                set_identifier_empty_exec(t, public, Ghost(consumed(st)));
                t.state = if public {
                    if c == 0x22 {
                        State::DoctypePublicIdentifierDoubleQuoted
                    } else {
                        State::DoctypePublicIdentifierSingleQuoted
                    }
                } else if c == 0x22 {
                    State::DoctypeSystemIdentifierDoubleQuoted
                } else {
                    State::DoctypeSystemIdentifierSingleQuoted
                };
            } else if c == 0x3E {
                consume_quirks_data_emit(input, t, out, Ghost(st));
            } else {
                quirks_bogus(t, Ghost(st));
            }
        },
    }
}

/// §13.2.5.58 Before DOCTYPE public identifier state.
pub fn before_doctype_public_identifier_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_doctype_public_identifier_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    before_doctype_identifier_state_exec(input, t, out, true, Ghost(st));
}

/// The four quoted DOCTYPE identifier states.
fn doctype_identifier_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    public: bool,
    quote: u32,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_identifier_quoted_state(input@, st, public, quote), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == quote {
                consume(input, t);
                t.state = if public {
                    State::AfterDoctypePublicIdentifier
                } else {
                    State::AfterDoctypeSystemIdentifier
                };
            } else if c == 0x3E {
                consume_quirks_data_emit(input, t, out, Ghost(st));
            } else {
                consume(input, t);
                append_to_identifier_exec(t, public, if c == 0x00 { 0xFFFD } else { c }, Ghost(consumed(st)));
            }
        },
    }
}

/// §13.2.5.59 DOCTYPE public identifier (double-quoted) state.
pub fn doctype_public_identifier_double_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_public_identifier_double_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    doctype_identifier_quoted_state_exec(input, t, out, true, 0x22, Ghost(st));
}

/// §13.2.5.60 DOCTYPE public identifier (single-quoted) state.
pub fn doctype_public_identifier_single_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_public_identifier_single_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    doctype_identifier_quoted_state_exec(input, t, out, true, 0x27, Ghost(st));
}

/// The after DOCTYPE public identifier and between identifiers states
/// (§13.2.5.61 and §13.2.5.62): `between` selects the second, where
/// whitespace is ignored instead of switching.
fn after_public_identifier_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    between: bool,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(
            if between {
                between_doctype_public_and_system_identifiers_state(input@, st)
            } else {
                after_doctype_public_identifier_state(input@, st)
            },
            final(t)@,
            old(out)@,
            final(out)@,
        ),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
                if !between {
                    t.state = State::BetweenDoctypePublicAndSystemIdentifiers;
                }
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else if c == 0x22 || c == 0x27 {
                consume(input, t);
                set_identifier_empty_exec(t, false, Ghost(consumed(st)));
                t.state = if c == 0x22 {
                    State::DoctypeSystemIdentifierDoubleQuoted
                } else {
                    State::DoctypeSystemIdentifierSingleQuoted
                };
            } else {
                quirks_bogus(t, Ghost(st));
            }
        },
    }
}

/// §13.2.5.61 After DOCTYPE public identifier state.
pub fn after_doctype_public_identifier_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_public_identifier_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    after_public_identifier_exec(input, t, out, false, Ghost(st));
}

/// §13.2.5.62 Between DOCTYPE public and system identifiers state.
pub fn between_doctype_public_and_system_identifiers_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(between_doctype_public_and_system_identifiers_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    after_public_identifier_exec(input, t, out, true, Ghost(st));
}

/// §13.2.5.63 After DOCTYPE system keyword state.
pub fn after_doctype_system_keyword_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_system_keyword_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    after_doctype_keyword_state_exec(input, t, out, false, Ghost(st));
}

/// §13.2.5.64 Before DOCTYPE system identifier state.
pub fn before_doctype_system_identifier_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(before_doctype_system_identifier_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    before_doctype_identifier_state_exec(input, t, out, false, Ghost(st));
}

/// §13.2.5.65 DOCTYPE system identifier (double-quoted) state.
pub fn doctype_system_identifier_double_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_system_identifier_double_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    doctype_identifier_quoted_state_exec(input, t, out, false, 0x22, Ghost(st));
}

/// §13.2.5.66 DOCTYPE system identifier (single-quoted) state.
pub fn doctype_system_identifier_single_quoted_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(doctype_system_identifier_single_quoted_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    doctype_identifier_quoted_state_exec(input, t, out, false, 0x27, Ghost(st));
}

/// §13.2.5.67 After DOCTYPE system identifier state.
pub fn after_doctype_system_identifier_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(after_doctype_system_identifier_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => quirks_eof(t, out, Ghost(st)),
        Some(c) => {
            if is_tab_lf_ff_space_exec(c) {
                consume(input, t);
            } else if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                t.state = State::BogusDoctype;
            }
        },
    }
}

/// §13.2.5.68 Bogus DOCTYPE state.
pub fn bogus_doctype_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(bogus_doctype_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_current_and_eof(t, out, Ghost(st)),
        Some(c) => {
            if c == 0x3E {
                consume_switch_to_data_and_emit(input, t, out, Ghost(st));
            } else {
                consume(input, t);
            }
        },
    }
}

} // verus!
