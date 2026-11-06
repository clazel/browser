//! The An+B microsyntax and its serialization, proven to meet [`super::contract`].
//!
//! `A` and `B` can be any integer, as long as the sheet likes. So the result keeps the
//! tokens they came from and says how to read each: what a number becomes is decided once,
//! by whoever uses it, as for every other number here.

use super::exec::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// How to read `A` or `B`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecPart {
    /// This number.
    Literal {
        /// The number.
        value: i8,
    },
    /// The value of the number or dimension at `index`, negated if `negated`.
    Value {
        /// Where it is in the tokens.
        index: usize,
        /// "the negation of the integer's value".
        negated: bool,
    },
    /// The digits after `from` of the ident or unit at `index`, which are negative: "the
    /// remainder interpreted as a base-10 number".
    Remainder {
        /// Where it is in the tokens.
        index: usize,
        /// Where its "-" is.
        from: usize,
    },
}

/// A parsed `<a-n-plus-b>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecAnB {
    /// Its tokens, without whitespace.
    pub tokens: Vec<ExecToken>,
    /// A.
    pub a: ExecPart,
    /// B.
    pub b: ExecPart,
}

/// The tokens as component values.
pub open spec fn as_values(tokens: Seq<ExecToken>) -> Seq<ComponentValue> {
    Seq::new(
        tokens.len(),
        |i: int|
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(tokens[i]) },
    )
}

/// The integer `part` stands for.
pub open spec fn view_part(tokens: Seq<ExecToken>, part: ExecPart) -> int {
    match part {
        ExecPart::Literal { value } => value as int,
        ExecPart::Value { index, negated } => {
            let token = crate::tokenizer::exec::view_token(tokens[index as int]);
            let value = match token {
                Token::Number { number } => integer_value(number),
                Token::Dimension { number, .. } => integer_value(number),
                _ => 0,
            };
            if negated {
                -value
            } else {
                value
            }
        },
        ExecPart::Remainder { index, from } => {
            let token = crate::tokenizer::exec::view_token(tokens[index as int]);
            match token {
                Token::Ident { value } => negative_remainder(value, from as int),
                Token::Dimension { unit, .. } => negative_remainder(unit, from as int),
                _ => 0,
            }
        },
    }
}

/// (A, B) of `tokens`.
pub open spec fn view_parts(
    tokens: Seq<ExecToken>,
    parts: Option<(ExecPart, ExecPart)>,
) -> Option<(int, int)> {
    match parts {
        Some((a, b)) => Some((view_part(tokens, a), view_part(tokens, b))),
        None => None,
    }
}

/// True if `token` is an `<ident-token>` matching `target`.
fn word_is(token: &ExecToken, target: &[u32]) -> (r: bool)
    ensures
        r == is_keyword(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
            target@,
        ),
{
    match token {
        ExecToken::Ident { value } => super::exec_declaration::matches_ignoring_case(
            value.as_slice(),
            target,
        ),
        _ => false,
    }
}

/// True if `token` is an integer `<dimension-token>` with a unit matching `target`.
fn dimension_is(token: &ExecToken, target: &[u32]) -> (r: bool)
    ensures
        r == (is_integer_dimension(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ) && ascii_case_insensitive_match(
            dimension_unit(
                ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
            ),
            target@,
        )),
{
    match token {
        ExecToken::Dimension { number, unit } => number.is_integer
            && super::exec_declaration::matches_ignoring_case(unit.as_slice(), target),
        _ => false,
    }
}

/// True if `token` is the `<delim-token>` `c`.
fn delim_is(token: &ExecToken, c: u32) -> (r: bool)
    ensures
        r == is(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
            Token::Delim { value: c },
        ),
{
    match token {
        ExecToken::Delim { value } => *value == c,
        _ => false,
    }
}

/// `n` and the digits after it, from `i`.
fn digits_from(string: &[u32], start: usize) -> (r: bool)
    ensures
        r == all_digits(string@, start as int),
{
    let mut i = start;
    while i < string.len()
        invariant
            start <= i,
            all_digits(string@, start as int) == all_digits(string@, i as int),
        decreases string.len() - i,
    {
        let c = crate::tokenizer::exec::peek(string, i);
        if !crate::tokenizer::exec::between(c, 0x30, 0x39) {
            proof {
                lemma_digit_fails(string@, start as int, i as int);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// [`all_digits`] is false before something else.
proof fn lemma_digit_fails(string: Seq<u32>, i: int, k: int)
    requires
        i <= k < string.len(),
        0 <= k,
        !is_digit(string[k]),
    ensures
        !all_digits(string, i),
    decreases k - i,
{
    if i < k {
        lemma_digit_fails(string, i + 1, k);
    }
}

/// [`is_n_dash_digits`].
fn n_dash_digits(string: &[u32], start: usize) -> (r: bool)
    requires
        start <= 1,
    ensures
        r == is_n_dash_digits(string@, start as int),
{
    let next = start.saturating_add(1);
    string.len() >= start.saturating_add(3) && super::exec_declaration::lowercase(
        crate::tokenizer::exec::peek(string, start),
    ) == 0x6E && crate::tokenizer::exec::peek(string, next) == 0x2D && digits_from(
        string,
        start.saturating_add(2),
    )
}

/// `<integer>`.
fn is_integer(token: &ExecToken) -> (r: bool)
    ensures
        r == (integer_number(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ) is Some),
{
    match token {
        ExecToken::Number { number } => number.is_integer,
        _ => false,
    }
}

/// `<signed-integer>`.
fn is_signed(token: &ExecToken) -> (r: bool)
    ensures
        r == (signed_integer(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ) is Some),
{
    match token {
        ExecToken::Number { number } => number.is_integer && number.sign_character.is_some(),
        _ => false,
    }
}

/// `<signless-integer>`.
fn is_signless(token: &ExecToken) -> (r: bool)
    ensures
        r == (signless_integer(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ) is Some),
{
    match token {
        ExecToken::Number { number } => number.is_integer && number.sign_character.is_none(),
        _ => false,
    }
}

/// [`a_of_n`], with what `A` is.
fn read_a_of_n(tokens: &[ExecToken], plus_adjacent: bool) -> (r: Option<(ExecPart, usize)>)
    ensures
        ({
            let items = as_values(tokens@);
            match r {
                Some((part, taken)) => a_of_n(items, plus_adjacent) == Some(
                    (view_part(tokens@, part), taken as int),
                ),
                None => a_of_n(items, plus_adjacent) is None,
            }
        }),
{
    let start: usize = 0;
    let n: [u32; 1] = [0x6E];
    let dash_n: [u32; 2] = [0x2D, 0x6E];
    proof {
        assert(n@ =~= n_string());
        assert(dash_n@ =~= dash_n_string());
    }
    let first = tokens.get(start)?;
    if dimension_is(first, n.as_slice()) {
        return Some((ExecPart::Value { index: 0, negated: false }, 1));
    }
    if word_is(first, n.as_slice()) {
        return Some((ExecPart::Literal { value: 1 }, 1));
    }
    if word_is(first, dash_n.as_slice()) {
        return Some((ExecPart::Literal { value: -1 }, 1));
    }
    let then_n = match tokens.get(1) {
        Some(second) => word_is(second, n.as_slice()),
        None => false,
    };
    if plus_adjacent && delim_is(first, 0x2B) && then_n {
        return Some((ExecPart::Literal { value: 1 }, 2));
    }
    None
}

/// [`a_of_n_dash`], with what `A` is.
fn read_a_of_n_dash(tokens: &[ExecToken], plus_adjacent: bool) -> (r: Option<(ExecPart, usize)>)
    ensures
        ({
            let items = as_values(tokens@);
            match r {
                Some((part, taken)) => a_of_n_dash(items, plus_adjacent) == Some(
                    (view_part(tokens@, part), taken as int),
                ),
                None => a_of_n_dash(items, plus_adjacent) is None,
            }
        }),
{
    let start: usize = 0;
    let n_dash: [u32; 2] = [0x6E, 0x2D];
    let dash_n_dash: [u32; 3] = [0x2D, 0x6E, 0x2D];
    proof {
        assert(n_dash@ =~= n_dash_string());
        assert(dash_n_dash@ =~= dash_n_dash_string());
    }
    let first = tokens.get(start)?;
    if dimension_is(first, n_dash.as_slice()) {
        return Some((ExecPart::Value { index: 0, negated: false }, 1));
    }
    if word_is(first, n_dash.as_slice()) {
        return Some((ExecPart::Literal { value: 1 }, 1));
    }
    if word_is(first, dash_n_dash.as_slice()) {
        return Some((ExecPart::Literal { value: -1 }, 1));
    }
    let then_n_dash = match tokens.get(1) {
        Some(second) => word_is(second, n_dash.as_slice()),
        None => false,
    };
    if plus_adjacent && delim_is(first, 0x2B) && then_n_dash {
        return Some((ExecPart::Literal { value: 1 }, 2));
    }
    None
}

/// [`single_clause`].
fn read_single_clause(tokens: &[ExecToken], plus_adjacent: bool) -> (r: Option<
    (ExecPart, ExecPart),
>)
    requires
        tokens.len() > 0,
    ensures
        view_parts(tokens@, r) == single_clause(as_values(tokens@), plus_adjacent),
{
    let count = tokens.len();
    let index = count.saturating_sub(1);
    let last = tokens.get(index)?;
    let start: usize = 0;
    let plussed = count == 2 && plus_adjacent && match tokens.get(start) {
        Some(first) => delim_is(first, 0x2B),
        None => false,
    };
    proof {
        assert(as_values(tokens@).last() == as_values(tokens@)[tokens.len() - 1]);
    }
    match last {
        ExecToken::Dimension { number, unit } => {
            if count == 1 && number.is_integer && n_dash_digits(unit.as_slice(), 0) {
                return Some(
                    (
                        ExecPart::Value { index, negated: false },
                        ExecPart::Remainder { index, from: 1 },
                    ),
                );
            }
            None
        },
        ExecToken::Ident { value } => {
            if (count == 1 || plussed) && n_dash_digits(value.as_slice(), 0) {
                return Some((ExecPart::Literal { value: 1 }, ExecPart::Remainder { index, from: 1 }));
            }
            if count == 1 && crate::tokenizer::exec::peek(value.as_slice(), 0) == 0x2D
                && n_dash_digits(value.as_slice(), 1) {
                return Some(
                    (ExecPart::Literal { value: -1 }, ExecPart::Remainder { index, from: 2 }),
                );
            }
            None
        },
        _ => None,
    }
}

/// [`a_n_plus_b_items`].
fn read_clauses(tokens: &[ExecToken], plus_adjacent: bool) -> (r: Option<(ExecPart, ExecPart)>)
    ensures
        view_parts(tokens@, r) == a_n_plus_b_items(as_values(tokens@), plus_adjacent),
{
    let odd: [u32; 3] = [0x6F, 0x64, 0x64];
    let even: [u32; 4] = [0x65, 0x76, 0x65, 0x6E];
    proof {
        assert(odd@ =~= seq![0x6Fu32, 0x64, 0x64]);
        assert(even@ =~= seq![0x65u32, 0x76, 0x65, 0x6E]);
    }
    let count = tokens.len();
    let start: usize = 0;
    let first = tokens.get(start)?;
    if count == 1 && word_is(first, odd.as_slice()) {
        return Some((ExecPart::Literal { value: 2 }, ExecPart::Literal { value: 1 }));
    }
    if count == 1 && word_is(first, even.as_slice()) {
        return Some((ExecPart::Literal { value: 2 }, ExecPart::Literal { value: 0 }));
    }
    if count == 1 && is_integer(first) {
        return Some(
            (ExecPart::Literal { value: 0 }, ExecPart::Value { index: 0, negated: false }),
        );
    }
    let last_index = count.saturating_sub(1);
    let last = tokens.get(last_index)?;
    proof {
        assert(as_values(tokens@).last() == as_values(tokens@)[tokens.len() - 1]);
    }
    match read_a_of_n(tokens, plus_adjacent) {
        Some((a, taken)) => {
            if count == taken {
                return Some((a, ExecPart::Literal { value: 0 }));
            }
            if count == taken.saturating_add(1) {
                if is_signed(last) {
                    return Some((a, ExecPart::Value { index: last_index, negated: false }));
                }
                return None;
            }
            if count == taken.saturating_add(2) && is_signless(last) {
                let operator = tokens.get(taken)?;
                if delim_is(operator, 0x2B) {
                    return Some((a, ExecPart::Value { index: last_index, negated: false }));
                }
                if delim_is(operator, 0x2D) {
                    return Some((a, ExecPart::Value { index: last_index, negated: true }));
                }
            }
            None
        },
        None => match read_a_of_n_dash(tokens, plus_adjacent) {
            Some((a, taken)) if count == taken.saturating_add(1) => {
                if is_signless(last) {
                    Some((a, ExecPart::Value { index: last_index, negated: true }))
                } else {
                    None
                }
            },
            _ => read_single_clause(tokens, plus_adjacent),
        },
    }
}

/// True if every item is a token.
pub open spec fn all_tokens(items: Seq<ComponentValue>) -> bool {
    forall|k: int| 0 <= k < items.len() ==> #[trigger] items[k] is Token
}

/// No clause of `<a-n-plus-b>` has more than four items, or anything but tokens.
proof fn lemma_clause_shape(items: Seq<ComponentValue>, plus_adjacent: bool)
    requires
        a_n_plus_b_items(items, plus_adjacent) is Some,
    ensures
        items.len() <= 4,
        all_tokens(items),
{
    assert forall|k: int| 0 <= k < items.len() implies #[trigger] items[k] is Token by {
        if items.len() >= 1 {
            assert(items.last() == items[items.len() - 1]);
        }
    }
}

/// What [`read_a_n_plus_b`] knows of a list so far.
pub open spec fn anb_list_ok(
    list: Seq<ComponentValue>,
    tokens: Seq<ExecToken>,
    too_long: bool,
    has_block: bool,
    state: u8,
    adjacent: bool,
) -> bool {
    let items = without_whitespace(list);
    let first = first_non_whitespace(list, 0);
    &&& !too_long && !has_block ==> as_values(tokens) == items
    &&& too_long ==> items.len() > 4
    &&& has_block ==> !all_tokens(items)
    &&& tokens.len() <= 4
    &&& (state == 0) == (first >= list.len())
    &&& (state == 1) == (first == list.len() - 1)
    &&& (state == 2) == (first < list.len() - 1)
    &&& adjacent == (first + 1 < list.len() && !is_whitespace_token(list[first + 1]))
}

/// [`without_whitespace`] of a list with one more item.
proof fn lemma_without_push(list: Seq<ComponentValue>, value: ComponentValue)
    ensures
        without_whitespace(list.push(value)) == if is_whitespace_token(value) {
            without_whitespace(list)
        } else {
            without_whitespace(list).push(value)
        },
{
    assert(list.push(value).drop_last() =~= list);
}

/// The state after one more item, in terms of what came before.
proof fn lemma_anb_step(
    list: Seq<ComponentValue>,
    tokens: Seq<ExecToken>,
    too_long: bool,
    has_block: bool,
    state: u8,
    adjacent: bool,
    value: ComponentValue,
    next_tokens: Seq<ExecToken>,
    next_too_long: bool,
    next_has_block: bool,
)
    requires
        anb_list_ok(list, tokens, too_long, has_block, state, adjacent),
        state <= 2,
        next_tokens.len() <= 4,
        !too_long && !has_block && !next_too_long && !next_has_block ==> as_values(next_tokens)
            == if is_whitespace_token(value) {
            as_values(tokens)
        } else {
            as_values(tokens).push(value)
        },
        too_long ==> next_too_long,
        has_block ==> next_has_block,
        next_too_long && !too_long ==> tokens.len() == 4 && !is_whitespace_token(value) && !(
        has_block),
        next_too_long && !too_long ==> as_values(tokens) == without_whitespace(list),
        next_has_block && !has_block ==> !(value is Token),
    ensures
        ({
            let bigger = list.push(value);
            let first = first_non_whitespace(list, 0);
            let whitespace = is_whitespace_token(value);
            let next_state: u8 = if state == 0 {
                if whitespace {
                    0
                } else {
                    1
                }
            } else {
                2
            };
            let next_adjacent = if state == 1 {
                !whitespace
            } else {
                adjacent
            };
            anb_list_ok(
                bigger,
                next_tokens,
                next_too_long,
                next_has_block,
                next_state,
                next_adjacent,
            )
        }),
{
    let bigger = list.push(value);
    let first = first_non_whitespace(list, 0);
    let items = without_whitespace(list);
    lemma_without_push(list, value);
    super::exec_rules::lemma_fnw_push(list, value, 0);
    if first + 1 < list.len() {
        assert(bigger[first + 1] == list[first + 1]);
    }
    if first < list.len() {
        assert(bigger[list.len() as int] == value);
    }
    if has_block {
        let bigger_items = without_whitespace(bigger);
        assert(!all_tokens(bigger_items)) by {
            let k = choose|k: int| 0 <= k < items.len() && !(#[trigger] items[k] is Token);
            if !is_whitespace_token(value) {
                assert(bigger_items[k] == items[k]);
            }
        }
    } else if next_has_block {
        let bigger_items = without_whitespace(bigger);
        assert(!is_whitespace_token(value));
        assert(!(bigger_items[items.len() as int] is Token));
    }
}

/// `tokens` with one more, as values.
proof fn lemma_values_push(tokens: Seq<ExecToken>, token: ExecToken)
    ensures
        as_values(tokens.push(token)) == as_values(tokens).push(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(token) },
        ),
{
    assert(as_values(tokens.push(token)) =~= as_values(tokens).push(
        ComponentValue::Token { token: crate::tokenizer::exec::view_token(token) },
    ));
}

/// (A, B) of a result.
pub open spec fn view_anb(result: Option<ExecAnB>) -> Option<(int, int)> {
    match result {
        Some(anb) => Some((view_part(anb.tokens@, anb.a), view_part(anb.tokens@, anb.b))),
        None => None,
    }
}

/// "Parse something according to a CSS grammar", the grammar being `<a-n-plus-b>`.
pub fn read_a_n_plus_b(input: &[u32]) -> (r: Option<ExecAnB>)
    requires
        parser_input_requires(input@),
    ensures
        a_n_plus_b_ensures(
            parse_a_list_of_component_values(Input::String { string: input@ }),
            view_anb(r),
        ),
{
    let text_vec = super::exec_parse::filtered(input);
    let text = text_vec.as_slice();
    let ghost stream = stream_of(text@, false);
    let ghost target = consume_a_list_of_component_values(stream, 0, None, false);
    let ghost mut list: Seq<ComponentValue> = Seq::empty();
    let mut tokens: Vec<ExecToken> = Vec::new();
    let mut too_long = false;
    let mut has_block = false;
    let mut state: u8 = 0;
    let mut adjacent = false;
    let mut at: usize = 0;
    let ghost mut idx: int = 0;
    proof {
        lemma_at_start(text@, false);
        assert(as_values(tokens@) =~= Seq::<ComponentValue>::empty());
        assert(first_non_whitespace(list, 0) == 0);
    }
    loop
        invariant
            super::exec_rules::text_fits(text@),
            stream == stream_of(text@, false),
            at_index(text@, false, idx, at as int),
            at <= text.len(),
            idx >= 0,
            state <= 2,
            anb_list_ok(list, tokens@, too_long, has_block, state, adjacent),
            list_of_component_values_loop(stream, idx, None, false, list) == target,
            target == consume_a_list_of_component_values(stream, 0, None, false),
            target.0 == parse_a_list_of_component_values(Input::String { string: input@ }),
        ensures
            is_empty(stream, idx),
        decreases tokens_left(text@, false, idx),
    {
        let ghost before_list = list;
        let ghost before_tokens = tokens@;
        let ghost was_long = too_long;
        let ghost was_block = has_block;
        let ghost was_state = state;
        let ghost was_adjacent = adjacent;
        let (token, next) = read_token(text, false, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Eof) {
            break;
        }
        let whitespace = matches!(token, ExecToken::Whitespace);
        let is_block = opens(&token);
        let ghost mut value = ComponentValue::Token { token: token_view };
        let mut end = next;
        if is_block {
            let mut scratch: Vec<ExecRow> = Vec::new();
            end = read_component_value(text, false, token, at, next, &mut scratch, Ghost(idx));
            has_block = true;
            proof {
                let k = scratch.len() - 1;
                value = consume_a_component_value(stream, idx).0;
                assert(scratch@[k] == scratch@.last());
                super::exec_declaration::lemma_value_kind(text@, scratch@, k, token_view);
                idx = consume_a_component_value(stream, idx).1;
            }
        } else {
            proof {
                super::termination::lemma_component_value_advances(stream, idx);
                idx = idx + 1;
            }
            if !whitespace && !too_long && !has_block {
                if tokens.len() == 4 {
                    too_long = true;
                } else {
                    tokens.push(token);
                    proof {
                        lemma_values_push(before_tokens, token);
                    }
                }
            }
        }
        proof {
            lemma_anb_step(
                before_list,
                before_tokens,
                was_long,
                was_block,
                was_state,
                was_adjacent,
                value,
                tokens@,
                too_long,
                has_block,
            );
            list = before_list.push(value);
        }
        if state == 1 {
            adjacent = !whitespace;
        }
        if state == 0 {
            if !whitespace {
                state = 1;
            }
        } else {
            state = 2;
        }
        at = end;
    }
    proof {
        assert(target == (list, idx));
        let items = without_whitespace(list);
        let first = first_non_whitespace(list, 0);
        assert(a_n_plus_b(list) == a_n_plus_b_items(items, adjacent));
        if a_n_plus_b_items(items, adjacent) is Some {
            lemma_clause_shape(items, adjacent);
        }
    }
    if too_long || has_block {
        return None;
    }
    let (a, b) = read_clauses(tokens.as_slice(), adjacent)?;
    Some(ExecAnB { tokens, a, b })
}

/// An integer, in sign and magnitude, for serialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecInteger {
    /// True if it is below zero, unless `magnitude` is zero.
    pub negative: bool,
    /// How far it is from zero.
    pub magnitude: u64,
}

/// The integer `value` stands for.
pub open spec fn view_integer(value: ExecInteger) -> int {
    if value.negative {
        -(value.magnitude as int)
    } else {
        value.magnitude as int
    }
}

/// `n`'s digits, on the end of `out`.
fn push_digits(n: u64, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + decimal_digits(n as nat, Seq::empty()),
{
    let ghost target = decimal_digits(n as nat, Seq::empty());
    let mut value = n;
    let mut digits: Vec<u32> = Vec::new();
    loop
        invariant_except_break
            decimal_digits(value as nat, digits@) == target,
        ensures
            digits@ == target,
        decreases value,
    {
        let ghost before = digits@;
        let digit = 0x30u32.saturating_add((value % 10) as u32);
        digits.insert(0, digit);
        proof {
            assert(digits@ =~= seq![digit] + before);
        }
        if value < 10 {
            break;
        }
        value /= 10;
    }
    let ghost start = out@;
    let mut i: usize = 0;
    proof {
        assert(digits@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(start + Seq::<u32>::empty() =~= start);
    }
    while i < digits.len()
        invariant
            i <= digits.len(),
            out@ == start + digits@.subrange(0, i as int),
        decreases digits.len() - i,
    {
        let ghost before = out@;
        out.push(crate::tokenizer::exec::peek(digits.as_slice(), i));
        i = i.saturating_add(1);
        proof {
            assert(out@ =~= start + digits@.subrange(0, i as int));
        }
    }
    proof {
        assert(digits@.subrange(0, digits.len() as int) =~= digits@);
    }
}

/// "the serialization of" `value`, on the end of `out`.
fn push_integer(value: ExecInteger, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + serialize_integer(view_integer(value)),
{
    let ghost start = out@;
    if value.negative && value.magnitude != 0 {
        out.push(0x2D);
        push_digits(value.magnitude, out);
        proof {
            let digits = decimal_digits(value.magnitude as nat, Seq::empty());
            assert(out@ =~= start + (seq![0x2Du32] + digits));
        }
    } else {
        push_digits(value.magnitude, out);
        proof {
            assert(view_integer(value) >= 0);
            assert(view_integer(value) as nat == value.magnitude as nat);
        }
    }
}

/// "Serialize an `<a-n-plus-b>` value".
pub fn write_a_n_plus_b(a: ExecInteger, b: ExecInteger) -> (r: Vec<u32>)
    ensures
        serialize_a_n_plus_b_ensures(view_integer(a), view_integer(b), r@),
{
    let mut out: Vec<u32> = Vec::new();
    if a.magnitude == 0 {
        push_integer(b, &mut out);
        proof {
            assert(out@ =~= serialize_integer(view_integer(b)));
        }
        return out;
    }
    if a.magnitude == 1 && !a.negative {
        out.push(0x6E);
    } else if a.magnitude == 1 {
        out.push(0x2D);
        out.push(0x6E);
    } else {
        push_integer(a, &mut out);
        out.push(0x6E);
    }
    let ghost result = out@;
    proof {
        if view_integer(a) == 1 {
            assert(result =~= seq![0x6Eu32]);
        } else if view_integer(a) == -1 {
            assert(result =~= seq![0x2Du32, 0x6E]);
        } else {
            assert(result =~= serialize_integer(view_integer(a)) + seq![0x6Eu32]);
        }
    }
    if b.magnitude == 0 {
        return out;
    }
    if !b.negative {
        out.push(0x2B);
    }
    push_integer(b, &mut out);
    proof {
        if view_integer(b) > 0 {
            assert(out@ =~= result + seq![0x2Bu32] + serialize_integer(view_integer(b)));
        } else {
            assert(out@ =~= result + serialize_integer(view_integer(b)));
        }
    }
    out
}

} // verus!
