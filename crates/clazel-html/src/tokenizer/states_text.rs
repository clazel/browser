//! The executable states §13.2.5.1 to §13.2.5.31 (text, tags, script
//! data), each proven equal to its spec function. The step comments live
//! in [`super::spec`].

use super::actions::*;
use super::buffer::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Is `c` tab, LF, FF or space.
pub fn is_tab_lf_ff_space_exec(c: u32) -> (r: bool)
    ensures
        r == is_tab_lf_ff_space(c),
{
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x20
}

/// Is `c` an ASCII upper alpha.
pub fn is_upper_exec(c: u32) -> (r: bool)
    ensures
        r == crate::charref::spec::is_ascii_upper_alpha(c),
{
    matches!(c, 0x41..=0x5A)
}

/// Is `c` an ASCII lower alpha.
pub fn is_lower_exec(c: u32) -> (r: bool)
    ensures
        r == crate::charref::spec::is_ascii_lower_alpha(c),
{
    matches!(c, 0x61..=0x7A)
}

/// Is `c` an ASCII alpha.
pub fn is_alpha_exec(c: u32) -> (r: bool)
    ensures
        r == crate::charref::spec::is_ascii_alpha(c),
{
    is_upper_exec(c) || is_lower_exec(c)
}

/// Advance past the current input character.
pub fn consume(_input: &[u32], t: &mut ExecTokenizer)
    requires
        old(t).pos < _input.len(),
    ensures
        final(t)@ == consumed(old(t)@),
{
    // Never saturates: pos < _input.len().
    t.pos = t.pos.saturating_add(1);
}

/// "Emit an end-of-file token" after nothing.
pub fn emit_eof_exec(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>)
    ensures
        final(t)@ == emit_eof(old(t)@, seq![]).0,
        tokens_view(final(out)@) =~= tokens_view(old(out)@) + emit_eof(old(t)@, seq![]).1,
{
    t.done = true;
    push_token(out, ExecToken::EndOfFile);
    assert(emit_eof(old(t)@, seq![]).1 =~= seq![Token::EndOfFile]);
}

/// The data, RCDATA, RAWTEXT, script data and PLAINTEXT states
/// (§13.2.5.1 to §13.2.5.5): `amp` is the return state on `&` (if the
/// state has that case), `lt` the state on `<` (if it has that case), and
/// `null_as_is` whether U+0000 is emitted as is.
fn text_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    amp: Option<ReturnState>,
    lt: Option<State>,
    null_as_is: bool,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        match next_char(input@, st.pos) {
            None => post(emit_eof(st, seq![]), final(t)@, old(out)@, final(out)@),
            Some(c) => if c == 0x26 && amp is Some {
                post(
                    none(switch_to(Tokenizer { return_state: amp.unwrap(), ..consumed(st) }, State::CharacterReference)),
                    final(t)@,
                    old(out)@,
                    final(out)@,
                )
            } else if c == 0x3C && lt is Some {
                post(none(switch_to(consumed(st), lt.unwrap())), final(t)@, old(out)@, final(out)@)
            } else if c == 0x00 {
                post(one(consumed(st), ch(if null_as_is { c } else { 0xFFFD })), final(t)@, old(out)@, final(out)@)
            } else {
                post(one(consumed(st), ch(c)), final(t)@, old(out)@, final(out)@)
            },
        },
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if c == 0x26 && amp.is_some() {
                if let Some(r) = amp {
                    t.return_state = r;
                }
                t.state = State::CharacterReference;
            } else if c == 0x3C && lt.is_some() {
                if let Some(s) = lt {
                    t.state = s;
                }
            } else if c == 0x00 {
                push_char(out, if null_as_is { c } else { 0xFFFD });
            } else {
                push_char(out, c);
            }
        },
    }
}

/// §13.2.5.1 Data state.
pub fn data_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(data_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_state_exec(input, t, out, Some(ReturnState::Data), Some(State::TagOpen), true, Ghost(st));
}

/// §13.2.5.2 RCDATA state.
pub fn rcdata_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rcdata_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_state_exec(input, t, out, Some(ReturnState::Rcdata), Some(State::RcdataLessThanSign), false, Ghost(st));
}

/// §13.2.5.3 RAWTEXT state.
pub fn rawtext_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rawtext_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_state_exec(input, t, out, None, Some(State::RawtextLessThanSign), false, Ghost(st));
}

/// §13.2.5.4 Script data state.
pub fn script_data_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_state_exec(input, t, out, None, Some(State::ScriptDataLessThanSign), false, Ghost(st));
}

/// §13.2.5.5 PLAINTEXT state.
pub fn plaintext_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(plaintext_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_state_exec(input, t, out, None, None, false, Ghost(st));
}

/// §13.2.5.6 Tag open state.
pub fn tag_open_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => {
            push_char(out, 0x3C);
            let ghost mid = out@;
            t.done = true;
            push_token(out, ExecToken::EndOfFile);
            assert(tag_open_state(input@, st).1 =~= seq![ch(0x3C), Token::EndOfFile]);
        },
        Some(c) => {
            if c == 0x21 {
                consume(input, t);
                t.state = State::MarkupDeclarationOpen;
            } else if c == 0x2F {
                consume(input, t);
                t.state = State::EndTagOpen;
            } else if is_alpha_exec(c) {
                new_start_tag_exec(t, Ghost(st));
                t.state = State::TagName;
            } else if c == 0x3F {
                consume(input, t);
                t.temporary_buffer = Vec::new();
                t.state = State::ProcessingInstructionOpen;
            } else {
                t.state = State::Data;
                push_char(out, 0x3C);
            }
        },
    }
}

/// §13.2.5.7 End tag open state.
pub fn end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(end_tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => {
            push_char(out, 0x3C);
            push_char(out, 0x2F);
            t.done = true;
            push_token(out, ExecToken::EndOfFile);
            assert(end_tag_open_state(input@, st).1 =~= seq![ch(0x3C), ch(0x2F), Token::EndOfFile]);
        },
        Some(c) => {
            if is_alpha_exec(c) {
                new_end_tag_exec(t, Ghost(st));
                t.state = State::TagName;
            } else if c == 0x3E {
                consume(input, t);
                t.state = State::Data;
            } else {
                new_comment_exec(t, Vec::new(), Ghost(st));
                t.state = State::BogusComment;
            }
        },
    }
}

/// §13.2.5.8 Tag name state.
pub fn tag_name_state_exec(input: &[u32], t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(tag_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            let ghost n = consumed(st);
            if is_tab_lf_ff_space_exec(c) {
                t.state = State::BeforeAttributeName;
            } else if c == 0x2F {
                t.state = State::SelfClosingStartTag;
            } else if c == 0x3E {
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(n, State::Data)));
            } else if is_upper_exec(c) {
                // Never overflows: c is at most 0x5A.
                append_to_tag_name_exec(t, c.saturating_add(0x20), Ghost(n));
            } else if c == 0x00 {
                append_to_tag_name_exec(t, 0xFFFD, Ghost(n));
            } else {
                append_to_tag_name_exec(t, c, Ghost(n));
            }
        },
    }
}

/// The "less-than sign" states of RCDATA and RAWTEXT.
fn text_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    text: State,
    end_tag_open: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(text_less_than_sign_state(input@, st, text, end_tag_open), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x2F) => {
            consume(input, t);
            t.temporary_buffer = Vec::new();
            t.state = end_tag_open;
        },
        _ => {
            t.state = text;
            push_char(out, 0x3C);
        },
    }
}

/// The "end tag open" states of RCDATA, RAWTEXT, script data and script
/// data escaped.
fn text_end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    text: State,
    end_tag_name: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(text_end_tag_open_state(input@, st, text, end_tag_name), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_alpha_exec(c) => {
            new_end_tag_exec(t, Ghost(st));
            t.state = end_tag_name;
        },
        _ => {
            t.state = text;
            push_char(out, 0x3C);
            push_char(out, 0x2F);
        },
    }
}

/// Is the current end tag token an appropriate end tag token.
pub fn is_appropriate_end_tag_exec(t: &ExecTokenizer) -> (r: bool)
    ensures
        r == is_appropriate_end_tag(t@),
{
    match (&t.current, &t.last_start_tag) {
        (ExecToken::EndTag { tag_name, .. }, Some(last)) => eq_codes(tag_name, last),
        _ => false,
    }
}

/// The "anything else" case of the end tag name states.
fn text_end_tag_name_anything_else(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, text: State)
    ensures
        final(t)@ == switch_to(old(t)@, text),
        tokens_view(final(out)@) =~= tokens_view(old(out)@) + (seq![ch(0x3C), ch(0x2F)] + chars(
            old(t)@.temporary_buffer,
        )),
{
    t.state = text;
    push_char(out, 0x3C);
    push_char(out, 0x2F);
    push_chars(out, &t.temporary_buffer);
}

/// The "end tag name" states of RCDATA, RAWTEXT, script data and script
/// data escaped.
fn text_end_tag_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    text: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(text_end_tag_name_state(input@, st, text), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        None => text_end_tag_name_anything_else(t, out, text),
        Some(c) => {
            let appropriate = is_appropriate_end_tag_exec(t);
            if is_tab_lf_ff_space_exec(c) && appropriate {
                consume(input, t);
                t.state = State::BeforeAttributeName;
            } else if c == 0x2F && appropriate {
                consume(input, t);
                t.state = State::SelfClosingStartTag;
            } else if c == 0x3E && appropriate {
                consume(input, t);
                t.state = State::Data;
                emit_current_tag_exec(t, out, Ghost(switch_to(consumed(st), State::Data)));
            } else if is_upper_exec(c) {
                consume(input, t);
                // Never overflows: c is at most 0x5A.
                append_to_tag_name_exec(t, c.saturating_add(0x20), Ghost(consumed(st)));
                t.temporary_buffer.push(c);
            } else if is_lower_exec(c) {
                consume(input, t);
                append_to_tag_name_exec(t, c, Ghost(consumed(st)));
                t.temporary_buffer.push(c);
            } else {
                text_end_tag_name_anything_else(t, out, text);
            }
        },
    }
}

/// §13.2.5.9 RCDATA less-than sign state.
pub fn rcdata_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rcdata_less_than_sign_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_less_than_sign_state_exec(input, t, out, State::Rcdata, State::RcdataEndTagOpen, Ghost(st));
}

/// §13.2.5.10 RCDATA end tag open state.
pub fn rcdata_end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rcdata_end_tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_open_state_exec(input, t, out, State::Rcdata, State::RcdataEndTagName, Ghost(st));
}

/// §13.2.5.11 RCDATA end tag name state.
pub fn rcdata_end_tag_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rcdata_end_tag_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_name_state_exec(input, t, out, State::Rcdata, Ghost(st));
}

/// §13.2.5.12 RAWTEXT less-than sign state.
pub fn rawtext_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rawtext_less_than_sign_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_less_than_sign_state_exec(input, t, out, State::Rawtext, State::RawtextEndTagOpen, Ghost(st));
}

/// §13.2.5.13 RAWTEXT end tag open state.
pub fn rawtext_end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rawtext_end_tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_open_state_exec(input, t, out, State::Rawtext, State::RawtextEndTagName, Ghost(st));
}

/// §13.2.5.14 RAWTEXT end tag name state.
pub fn rawtext_end_tag_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(rawtext_end_tag_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_name_state_exec(input, t, out, State::Rawtext, Ghost(st));
}

/// §13.2.5.15 Script data less-than sign state.
pub fn script_data_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_less_than_sign_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x2F) => {
            consume(input, t);
            t.temporary_buffer = Vec::new();
            t.state = State::ScriptDataEndTagOpen;
        },
        Some(0x21) => {
            consume(input, t);
            t.state = State::ScriptDataEscapeStart;
            push_char(out, 0x3C);
            push_char(out, 0x21);
        },
        _ => {
            t.state = State::ScriptData;
            push_char(out, 0x3C);
        },
    }
}

/// §13.2.5.16 Script data end tag open state.
pub fn script_data_end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_end_tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_open_state_exec(input, t, out, State::ScriptData, State::ScriptDataEndTagName, Ghost(st));
}

/// §13.2.5.17 Script data end tag name state.
pub fn script_data_end_tag_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_end_tag_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_name_state_exec(input, t, out, State::ScriptData, Ghost(st));
}

/// The script data escape start and escape start dash states (§13.2.5.18
/// and §13.2.5.19): on `-` switch to `next` and emit `-`.
fn escape_start_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    next: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        match next_char(input@, st.pos) {
            Some(c) if c == 0x2D => post(one(switch_to(consumed(st), next), ch(0x2D)), final(t)@, old(out)@, final(out)@),
            _ => post(none(switch_to(st, State::ScriptData)), final(t)@, old(out)@, final(out)@),
        },
{
    match next_char_exec(input, t.pos) {
        Some(0x2D) => {
            consume(input, t);
            t.state = next;
            push_char(out, 0x2D);
        },
        _ => {
            t.state = State::ScriptData;
        },
    }
}

/// §13.2.5.18 Script data escape start state.
pub fn script_data_escape_start_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escape_start_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escape_start_exec(input, t, out, State::ScriptDataEscapeStartDash, Ghost(st));
}

/// §13.2.5.19 Script data escape start dash state.
pub fn script_data_escape_start_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escape_start_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escape_start_exec(input, t, out, State::ScriptDataEscapedDashDash, Ghost(st));
}

/// The script data escaped and double escaped states and their dash and
/// dash dash states (§13.2.5.20 to §13.2.5.22, §13.2.5.27 to §13.2.5.29).
/// `double` selects the double escaped family, `dashes` is 0, 1 or 2.
fn escaped_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    double: bool,
    dashes: u8,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
        dashes <= 2,
    ensures
        post(escaped_step(input@, st, double, dashes), final(t)@, old(out)@, final(out)@),
{
    let base = if double { State::ScriptDataDoubleEscaped } else { State::ScriptDataEscaped };
    let lt = if double { State::ScriptDataDoubleEscapedLessThanSign } else { State::ScriptDataEscapedLessThanSign };
    match next_char_exec(input, t.pos) {
        None => emit_eof_exec(t, out),
        Some(c) => {
            consume(input, t);
            if c == 0x2D {
                if dashes == 0 {
                    t.state = if double { State::ScriptDataDoubleEscapedDash } else { State::ScriptDataEscapedDash };
                } else if dashes == 1 {
                    t.state = if double {
                        State::ScriptDataDoubleEscapedDashDash
                    } else {
                        State::ScriptDataEscapedDashDash
                    };
                }
                push_char(out, 0x2D);
            } else if c == 0x3C {
                t.state = lt;
                if double {
                    push_char(out, 0x3C);
                }
            } else if c == 0x3E && dashes == 2 {
                t.state = State::ScriptData;
                push_char(out, 0x3E);
            } else {
                t.state = base;
                push_char(out, if c == 0x00 { 0xFFFD } else { c });
            }
        },
    }
}

/// The six escaped states, as one spec function of their two parameters
/// (proven equal to each state's own spec function below).
pub open spec fn escaped_step(input: Seq<u32>, st: Tokenizer, double: bool, dashes: u8) -> Step {
    let base = if double { State::ScriptDataDoubleEscaped } else { State::ScriptDataEscaped };
    let lt = if double { State::ScriptDataDoubleEscapedLessThanSign } else { State::ScriptDataEscapedLessThanSign };
    match next_char(input, st.pos) {
        None => emit_eof(st, seq![]),
        Some(c) => {
            let n = consumed(st);
            if c == 0x2D {
                if dashes == 0 {
                    one(
                        switch_to(n, if double { State::ScriptDataDoubleEscapedDash } else { State::ScriptDataEscapedDash }),
                        ch(0x2D),
                    )
                } else if dashes == 1 {
                    one(
                        switch_to(
                            n,
                            if double {
                                State::ScriptDataDoubleEscapedDashDash
                            } else {
                                State::ScriptDataEscapedDashDash
                            },
                        ),
                        ch(0x2D),
                    )
                } else {
                    one(n, ch(0x2D))
                }
            } else if c == 0x3C {
                if double {
                    one(switch_to(n, lt), ch(0x3C))
                } else {
                    none(switch_to(n, lt))
                }
            } else if c == 0x3E && dashes == 2 {
                one(switch_to(n, State::ScriptData), ch(0x3E))
            } else if c == 0x00 {
                one(switch_to(n, base), ch(0xFFFD))
            } else {
                one(switch_to(n, base), ch(c))
            }
        },
    }
}

/// §13.2.5.20 Script data escaped state.
pub fn script_data_escaped_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
        st.state is ScriptDataEscaped,
    ensures
        post(script_data_escaped_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, false, 0, Ghost(st));
}

/// §13.2.5.21 Script data escaped dash state.
pub fn script_data_escaped_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escaped_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, false, 1, Ghost(st));
}

/// §13.2.5.22 Script data escaped dash dash state.
pub fn script_data_escaped_dash_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escaped_dash_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, false, 2, Ghost(st));
}

/// §13.2.5.23 Script data escaped less-than sign state.
pub fn script_data_escaped_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escaped_less_than_sign_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x2F) => {
            consume(input, t);
            t.temporary_buffer = Vec::new();
            t.state = State::ScriptDataEscapedEndTagOpen;
        },
        Some(c) if is_alpha_exec(c) => {
            t.temporary_buffer = Vec::new();
            t.state = State::ScriptDataDoubleEscapeStart;
            push_char(out, 0x3C);
        },
        _ => {
            t.state = State::ScriptDataEscaped;
            push_char(out, 0x3C);
        },
    }
}

/// §13.2.5.24 Script data escaped end tag open state.
pub fn script_data_escaped_end_tag_open_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escaped_end_tag_open_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_open_state_exec(
        input,
        t,
        out,
        State::ScriptDataEscaped,
        State::ScriptDataEscapedEndTagName,
        Ghost(st),
    );
}

/// §13.2.5.25 Script data escaped end tag name state.
pub fn script_data_escaped_end_tag_name_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_escaped_end_tag_name_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    text_end_tag_name_state_exec(input, t, out, State::ScriptDataEscaped, Ghost(st));
}

/// The script data double escape start and end states.
fn double_escape_boundary_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    if_script: State,
    otherwise: State,
    anything_else: State,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(
            double_escape_boundary_state(input@, st, if_script, otherwise, anything_else),
            final(t)@,
            old(out)@,
            final(out)@,
        ),
{
    match next_char_exec(input, t.pos) {
        Some(c) if is_tab_lf_ff_space_exec(c) || c == 0x2F || c == 0x3E => {
            let script = from_slice([0x73u32, 0x63, 0x72, 0x69, 0x70, 0x74].as_slice());
            assert(script@ =~= super::spec::script());
            let is_script = eq_codes(&t.temporary_buffer, &script);
            consume(input, t);
            t.state = if is_script { if_script } else { otherwise };
            push_char(out, c);
        },
        Some(c) if is_upper_exec(c) => {
            consume(input, t);
            // Never overflows: c is at most 0x5A.
            t.temporary_buffer.push(c.saturating_add(0x20));
            push_char(out, c);
        },
        Some(c) if is_lower_exec(c) => {
            consume(input, t);
            t.temporary_buffer.push(c);
            push_char(out, c);
        },
        _ => {
            t.state = anything_else;
        },
    }
}

/// §13.2.5.26 Script data double escape start state.
pub fn script_data_double_escape_start_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_double_escape_start_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    double_escape_boundary_state_exec(
        input,
        t,
        out,
        State::ScriptDataDoubleEscaped,
        State::ScriptDataEscaped,
        State::ScriptDataEscaped,
        Ghost(st),
    );
}

/// §13.2.5.27 Script data double escaped state.
pub fn script_data_double_escaped_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
        st.state is ScriptDataDoubleEscaped,
    ensures
        post(script_data_double_escaped_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, true, 0, Ghost(st));
}

/// §13.2.5.28 Script data double escaped dash state.
pub fn script_data_double_escaped_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_double_escaped_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, true, 1, Ghost(st));
}

/// §13.2.5.29 Script data double escaped dash dash state.
pub fn script_data_double_escaped_dash_dash_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_double_escaped_dash_dash_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    escaped_exec(input, t, out, true, 2, Ghost(st));
}

/// §13.2.5.30 Script data double escaped less-than sign state.
pub fn script_data_double_escaped_less_than_sign_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_double_escaped_less_than_sign_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    match next_char_exec(input, t.pos) {
        Some(0x2F) => {
            consume(input, t);
            t.temporary_buffer = Vec::new();
            t.state = State::ScriptDataDoubleEscapeEnd;
            push_char(out, 0x2F);
        },
        _ => {
            t.state = State::ScriptDataDoubleEscaped;
        },
    }
}

/// §13.2.5.31 Script data double escape end state.
pub fn script_data_double_escape_end_state_exec(
    input: &[u32],
    t: &mut ExecTokenizer,
    out: &mut Vec<ExecToken>,
    Ghost(st): Ghost<Tokenizer>,
)
    requires
        pre(input@, st, old(t)@),
    ensures
        post(script_data_double_escape_end_state(input@, st), final(t)@, old(out)@, final(out)@),
{
    double_escape_boundary_state_exec(
        input,
        t,
        out,
        State::ScriptDataEscaped,
        State::ScriptDataDoubleEscaped,
        State::ScriptDataDoubleEscaped,
        Ghost(st),
    );
}

} // verus!
