//! The loops of the parser that read component values one after another: "discard
//! whitespace", "consume a list of component values" and "consume the remnants of a bad
//! declaration". Each is one `loop` around [`super::exec::read_component_value`], whose
//! invariant is that the spec's loop gives the same from here.

use super::exec::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The stop token, as a number: 0 is none, 1 is `<semicolon-token>` and 2 `<comma-token>`.
pub open spec fn stop_token(stop: u8) -> Option<Token> {
    if stop == 1 {
        Some(Token::Semicolon)
    } else if stop == 2 {
        Some(Token::Comma)
    } else {
        None
    }
}

/// True if `token` is the [`stop_token`] `stop`.
pub fn is_stop_token(token: &ExecToken, stop: u8) -> (r: bool)
    ensures
        r == is_stop(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
            stop_token(stop),
        ),
{
    match token {
        ExecToken::Semicolon => stop == 1,
        ExecToken::Comma => stop == 2,
        _ => false,
    }
}

/// "Discard whitespace".
pub fn skip_whitespace(text: &[u32], flag: bool, pos: usize, Ghost(index): Ghost<int>) -> (r: (
    usize,
    Ghost<int>,
))
    requires
        text_requires(text@),
        at_index(text@, flag, index, pos as int),
        pos <= text.len(),
    ensures
        r.1@ == discard_whitespace(stream_of(text@, flag), index),
        at_index(text@, flag, r.1@, r.0 as int),
        pos <= r.0 <= text.len(),
        r.1@ >= index,
{
    let ghost input = stream_of(text@, flag);
    let mut at = pos;
    let ghost mut idx = index;
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, flag),
            at_index(text@, flag, idx, at as int),
            pos <= at <= text.len(),
            index <= idx,
            discard_whitespace(input, idx) == discard_whitespace(input, index),
        decreases tokens_left(text@, flag, idx),
    {
        let (token, next) = read_token(text, flag, at, Ghost(idx));
        if matches!(token, ExecToken::Whitespace) {
            at = next;
            proof {
                idx = idx + 1;
            }
        } else {
            return (at, Ghost(idx));
        }
    }
}

/// Reading a value added it to the end of every list of `rows`.
pub proof fn lemma_value_added(
    text: Seq<u32>,
    flag: bool,
    old: Seq<ExecRow>,
    new: Seq<ExecRow>,
    lo: int,
    value: ComponentValue,
)
    requires
        0 <= lo <= old.len(),
        new.len() > old.len(),
        extends(old, new),
        new.last().start == old.len(),
        view_value(text, flag, new, new.len() - 1) == value,
    ensures
        view_list(text, flag, new, lo, new.len() as int) == view_list(
            text,
            flag,
            old,
            lo,
            old.len() as int,
        ).push(value),
{
    assert(new[new.len() - 1] == new.last());
    assert(view_list(text, flag, new, lo, new.len() as int) == view_list(
        text,
        flag,
        new,
        lo,
        new.last().start as int,
    ).push(view_value(text, flag, new, new.len() - 1))) by {
        if new.len() as int - 1 == old.len() as int {
        } else {
        }
    }
    lemma_agree_list(text, flag, old, new, lo, old.len() as int);
}

/// Pushing the row of a token that opens nothing adds that token.
pub proof fn lemma_token_added(
    text: Seq<u32>,
    flag: bool,
    old: Seq<ExecRow>,
    lo: int,
    pos: u32,
    token: Token,
)
    requires
        0 <= lo <= old.len(),
        old.len() < u32::MAX,
        token_at(text, flag, pos as int) == token,
        !opens_a_value(token),
    ensures
        ({
            let new = old.push(ExecRow { pos, start: old.len() as u32 });
            &&& extends(old, new)
            &&& view_value(text, flag, new, old.len() as int) == (ComponentValue::Token { token })
            &&& view_list(text, flag, new, lo, new.len() as int) == view_list(
                text,
                flag,
                old,
                lo,
                old.len() as int,
            ).push(ComponentValue::Token { token })
        }),
{
    let new = old.push(ExecRow { pos, start: old.len() as u32 });
    assert(new[old.len() as int] == new.last());
    assert forall|k: int| 0 <= k < old.len() implies old[k] == new[k] by {}
    assert(view_value(text, flag, new, old.len() as int) == (ComponentValue::Token { token }));
    lemma_value_added(text, flag, old, new, lo, ComponentValue::Token { token });
}

/// "Consume a list of component values". Its values go on the end of `rows`.
pub fn read_list(
    text: &[u32],
    flag: bool,
    pos: usize,
    stop: u8,
    nested: bool,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
) -> (r: (usize, Ghost<int>))
    requires
        text_requires(text@),
        at_index(text@, flag, index, pos as int),
        pos <= text.len(),
        rows_fit(text@, flag, old(rows).len() as nat, index),
    ensures
        ({
            let (list, after) = consume_a_list_of_component_values(
                stream_of(text@, flag),
                index,
                stop_token(stop),
                nested,
            );
            &&& r.1@ == after
            &&& at_index(text@, flag, after, r.0 as int)
            &&& extends(old(rows)@, final(rows)@)
            &&& old(rows).len() <= final(rows).len()
            &&& view_list(
                text@,
                flag,
                final(rows)@,
                old(rows).len() as int,
                final(rows).len() as int,
            ) == list
            &&& paid(text@, flag, old(rows).len() as nat, index, final(rows).len() as nat, after)
            &&& after >= index
            &&& pos <= r.0 <= text.len()
        }),
{
    let ghost input = stream_of(text@, flag);
    let ghost lo = rows.len() as int;
    let ghost old_rows = rows@;
    let ghost target = consume_a_list_of_component_values(input, index, stop_token(stop), nested);
    let mut at = pos;
    let ghost mut idx = index;
    proof {
        assert(view_list(text@, flag, rows@, lo, lo) =~= Seq::<ComponentValue>::empty());
        assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {}
    }
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, flag),
            at_index(text@, flag, idx, at as int),
            pos <= at <= text.len(),
            index <= idx,
            lo == old_rows.len(),
            old_rows == old(rows)@,
            extends(old_rows, rows@),
            lo <= rows.len(),
            paid(text@, flag, old_rows.len() as nat, index, rows.len() as nat, idx),
            rows_fit(text@, flag, old_rows.len() as nat, index),
            list_of_component_values_loop(
                input,
                idx,
                stop_token(stop),
                nested,
                view_list(text@, flag, rows@, lo, rows.len() as int),
            ) == target,
            target == consume_a_list_of_component_values(input, index, stop_token(stop), nested),
        decreases tokens_left(text@, flag, idx),
    {
        let ghost values = view_list(text@, flag, rows@, lo, rows.len() as int);
        let ghost before = rows@;
        let (token, next) = read_token(text, flag, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Eof) || is_stop_token(&token, stop) {
            return (at, Ghost(idx));
        } else if matches!(token, ExecToken::CloseCurly) {
            if nested {
                return (at, Ghost(idx));
            }
            let start = rows.len() as u32;
            rows.push(ExecRow { pos: at as u32, start });
            proof {
                lemma_token_added(text@, flag, before, lo, at as u32, token_view);
                lemma_extends_chain(old_rows, before, rows@);
                idx = idx + 1;
            }
            at = next;
        } else {
            let end = read_component_value(text, flag, token, at, next, rows, Ghost(idx));
            proof {
                let (value, after) = consume_a_component_value(input, idx);
                lemma_value_added(text@, flag, before, rows@, lo, value);
                lemma_extends_chain(old_rows, before, rows@);
                idx = after;
            }
            at = end;
        }
    }
}

/// [`extends`] goes through a row list between.
pub proof fn lemma_extends_chain(a: Seq<ExecRow>, b: Seq<ExecRow>, c: Seq<ExecRow>)
    requires
        extends(a, b),
        extends(b, c),
        a.len() <= b.len(),
    ensures
        extends(a, c),
{
    assert forall|k: int| 0 <= k < a.len() implies a[k] == c[k] by {
        assert(a[k] == b[k]);
        assert(b[k] == c[k]);
    }
}

/// "Consume the remnants of a bad declaration".
pub fn read_remnants(
    text: &[u32],
    flag: bool,
    pos: usize,
    nested: bool,
    Ghost(index): Ghost<int>,
) -> (r: (usize, Ghost<int>))
    requires
        text_requires(text@),
        at_index(text@, flag, index, pos as int),
        pos <= text.len(),
        rows_fit(text@, flag, 0, index),
    ensures
        r.1@ == consume_the_remnants_of_a_bad_declaration(stream_of(text@, flag), index, nested),
        at_index(text@, flag, r.1@, r.0 as int),
        pos <= r.0 <= text.len(),
        r.1@ >= index,
{
    let ghost input = stream_of(text@, flag);
    let ghost target = consume_the_remnants_of_a_bad_declaration(input, index, nested);
    let mut at = pos;
    let ghost mut idx = index;
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, flag),
            at_index(text@, flag, idx, at as int),
            pos <= at <= text.len(),
            index <= idx,
            rows_fit(text@, flag, 0, index),
            consume_the_remnants_of_a_bad_declaration(input, idx, nested) == target,
            target == consume_the_remnants_of_a_bad_declaration(input, index, nested),
        decreases tokens_left(text@, flag, idx),
    {
        let (token, next) = read_token(text, flag, at, Ghost(idx));
        if matches!(token, ExecToken::Eof) {
            return (at, Ghost(idx));
        } else if matches!(token, ExecToken::Semicolon) {
            return (next, Ghost(idx + 1));
        } else if matches!(token, ExecToken::CloseCurly) {
            if nested {
                return (at, Ghost(idx));
            }
            at = next;
            proof {
                idx = idx + 1;
            }
        } else {
            let mut scratch: Vec<ExecRow> = Vec::new();
            let end = read_component_value(text, flag, token, at, next, &mut scratch, Ghost(idx));
            proof {
                idx = consume_a_component_value(input, idx).1;
            }
            at = end;
        }
    }
}

} // verus!
