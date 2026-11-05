//! "Consume a declaration", proven to meet [`super::contract`].
//!
//! One pass reads the value. Steps 6 to 8 look at its last items, so the pass keeps a
//! [`Mark`] after each of the last three non-whitespace items: everything steps 6 and 7 can
//! remove lies after one of them, and a mark says what comes before it.
//!
//! When the caller will go back and reparse as a rule, nothing that follows a failure
//! matters, so two of the "early exits" of the text's implementation note apply: no
//! remnants are read, and a name that is not custom stops at a `{` with a value before it.
//! That is what makes `a:b{a:b{…` linear.

#[allow(unused_imports)]
use super::contract::{at_index, position_of};
use super::exec::*;
use super::exec_lists::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Facts about the last items of a list
// ------------------------------------------------------------------------------------

/// What [`last_non_whitespace`] finds.
pub proof fn lemma_lnw(value: Seq<ComponentValue>, end: int)
    requires
        end <= value.len(),
    ensures
        -1 <= last_non_whitespace(value, end),
        end > 0 ==> last_non_whitespace(value, end) < end,
        end <= 0 ==> last_non_whitespace(value, end) == -1,
        last_non_whitespace(value, end) >= 0 ==> !is_whitespace_token(
            value[last_non_whitespace(value, end)],
        ),
        forall|k: int|
            last_non_whitespace(value, end) < k < end && 0 <= k ==> is_whitespace_token(
                #[trigger] value[k],
            ),
    decreases end,
{
    if end > 0 && is_whitespace_token(value[end - 1]) {
        lemma_lnw(value, end - 1);
    }
}

/// [`last_non_whitespace`] is the item it says it is.
pub proof fn lemma_lnw_is(value: Seq<ComponentValue>, end: int, c: int)
    requires
        end <= value.len(),
        -1 <= c,
        c < end || (c == -1 && end <= 0),
        c >= 0 ==> !is_whitespace_token(value[c]),
        forall|k: int| c < k < end && 0 <= k ==> is_whitespace_token(#[trigger] value[k]),
    ensures
        last_non_whitespace(value, end) == c,
    decreases end,
{
    if end > 0 && c < end - 1 {
        assert(is_whitespace_token(value[end - 1]));
        lemma_lnw_is(value, end - 1, c);
    }
}

/// [`without_trailing_whitespace`] stops at the last item that is not whitespace.
pub proof fn lemma_trailing(value: Seq<ComponentValue>)
    ensures
        without_trailing_whitespace(value) == value.subrange(
            0,
            last_non_whitespace(value, value.len() as int) + 1,
        ),
    decreases value.len(),
{
    lemma_lnw(value, value.len() as int);
    if value.len() > 0 && is_whitespace_token(value.last()) {
        let shorter = value.drop_last();
        lemma_trailing(shorter);
        lemma_lnw(value, shorter.len() as int);
        let c = last_non_whitespace(value, shorter.len() as int);
        assert forall|k: int| c < k < shorter.len() && 0 <= k implies is_whitespace_token(
            #[trigger] shorter[k],
        ) by {
            assert(shorter[k] == value[k]);
            assert(is_whitespace_token(value[k]));
        }
        if c >= 0 {
            assert(shorter[c] == value[c]);
        }
        lemma_lnw_is(shorter, shorter.len() as int, c);
        assert(shorter.subrange(0, c + 1) =~= value.subrange(0, c + 1));
    } else if value.len() > 0 {
        assert(value.subrange(0, value.len() as int) =~= value);
    } else {
        assert(value.subrange(0, 0) =~= value);
    }
}

/// What steps 6 and 7 of "consume a declaration" leave of `list`.
pub open spec fn trimmed(list: Seq<ComponentValue>) -> Seq<ComponentValue> {
    let value = match important_at(list) {
        Some((first, second)) => list.remove(second).remove(first),
        None => list,
    };
    without_trailing_whitespace(value)
}

/// How many items of `list` steps 6 and 7 leave.
pub open spec fn kept_items(list: Seq<ComponentValue>) -> int {
    match important_at(list) {
        Some((first, second)) => last_non_whitespace(list, first) + 1,
        None => last_non_whitespace(list, list.len() as int) + 1,
    }
}

/// Steps 6 and 7 only remove from the end.
pub proof fn lemma_trimmed(list: Seq<ComponentValue>)
    ensures
        0 <= kept_items(list) <= list.len(),
        trimmed(list) == list.subrange(0, kept_items(list)),
{
    let n = list.len() as int;
    lemma_lnw(list, n);
    match important_at(list) {
        None => {
            lemma_trailing(list);
        },
        Some((a, b)) => {
            assert(b == last_non_whitespace(list, n));
            lemma_lnw(list, b);
            assert(a == last_non_whitespace(list, b));
            lemma_lnw(list, a);
            let x = list.remove(b).remove(a);
            let c = last_non_whitespace(list, a);
            lemma_trailing(x);
            assert(x.len() == n - 2);
            assert forall|k: int| 0 <= k < a implies #[trigger] x[k] == list[k] by {}
            assert forall|k: int| c < k < x.len() && 0 <= k implies is_whitespace_token(
                #[trigger] x[k],
            ) by {
                if k < a {
                    assert(x[k] == list[k]);
                } else if k + 1 < b {
                    assert(x[k] == list[k + 1]);
                    assert(a < k + 1 < b);
                    assert(is_whitespace_token(list[k + 1]));
                } else {
                    assert(x[k] == list[k + 2]);
                    assert(b < k + 2 < n);
                    assert(is_whitespace_token(list[k + 2]));
                }
            }
            if c >= 0 {
                assert(x[c] == list[c]);
            }
            lemma_lnw_is(x, x.len() as int, c);
            assert(x.subrange(0, c + 1) =~= list.subrange(0, c + 1));
        },
    }
}

/// [`has_curly_block`] finds the block at `y`.
proof fn lemma_has_curly(value: Seq<ComponentValue>, i: int, y: int)
    requires
        0 <= i <= y < value.len(),
        is_curly_block(value[y]),
    ensures
        has_curly_block(value, i),
    decreases y - i,
{
    if i < y {
        lemma_has_curly(value, i + 1, y);
    }
}

/// [`non_whitespace_count`] counts what is there.
proof fn lemma_count_one(value: Seq<ComponentValue>, i: int, y: int)
    requires
        0 <= i <= y < value.len(),
        !is_whitespace_token(value[y]),
    ensures
        non_whitespace_count(value, i) >= 1,
    decreases y - i,
{
    if i < y {
        lemma_count_one(value, i + 1, y);
    }
}

/// [`non_whitespace_count`] counts two items.
proof fn lemma_count_two(value: Seq<ComponentValue>, i: int, x: int, y: int)
    requires
        0 <= i <= x < y < value.len(),
        !is_whitespace_token(value[x]),
        !is_whitespace_token(value[y]),
    ensures
        non_whitespace_count(value, i) >= 2,
    decreases x - i,
{
    if i < x {
        lemma_count_two(value, i + 1, x, y);
    } else {
        lemma_count_one(value, i + 1, y);
    }
}

/// A value before a `{}` block survives steps 6 and 7, and so does the block, so step 8
/// says "return nothing".
proof fn lemma_block_and_another(list: Seq<ComponentValue>, x: int, y: int)
    requires
        0 <= x < y < list.len(),
        !is_whitespace_token(list[x]),
        is_curly_block(list[y]),
    ensures
        has_curly_block_and_another(trimmed(list)),
{
    let n = list.len() as int;
    lemma_trimmed(list);
    lemma_lnw(list, n);
    let b = last_non_whitespace(list, n);
    assert(!is_whitespace_token(list[y]));
    assert(b >= y) by {
        if b < y {
            assert(is_whitespace_token(list[y]));
        }
    }
    let value = trimmed(list);
    match important_at(list) {
        None => {
            assert(kept_items(list) == b + 1);
        },
        Some((a0, b0)) => {
            assert(b0 == b);
            assert(is_ident(list[b]));
            assert(b > y);
            lemma_lnw(list, b);
            assert(a0 == last_non_whitespace(list, b));
            assert(a0 >= y) by {
                if a0 < y {
                    assert(is_whitespace_token(list[y]));
                }
            }
            assert(is(list[a0], Token::Delim { value: 0x21 }));
            assert(a0 > y);
            lemma_lnw(list, a0);
            let c = last_non_whitespace(list, a0);
            assert(c >= y) by {
                if c < y {
                    assert(is_whitespace_token(list[y]));
                }
            }
            assert(kept_items(list) == c + 1);
        },
    }
    assert(value[y] == list[y]);
    assert(value[x] == list[x]);
    lemma_has_curly(value, 0, y);
    lemma_count_two(value, 0, x, y);
}

/// A simple block's loop gives a simple block with that token.
proof fn lemma_block_shape(
    input: TokenStream,
    index: int,
    ending_token: Token,
    associated_token: Token,
    value: Seq<ComponentValue>,
)
    ensures
        simple_block_loop(input, index, ending_token, associated_token, value).0 is SimpleBlock,
        simple_block_loop(
            input,
            index,
            ending_token,
            associated_token,
            value,
        ).0->SimpleBlock_associated_token == associated_token,
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, ending_token)) {
        let (component_value, next) = consume_a_component_value(input, index);
        lemma_block_shape(
            input,
            moved(index, next),
            ending_token,
            associated_token,
            value.push(component_value),
        );
    }
}

/// The list loop keeps what it was given.
proof fn lemma_list_keeps(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
    values: Seq<ComponentValue>,
)
    ensures
        ({
            let list = list_of_component_values_loop(input, index, stop_token, nested, values).0;
            &&& list.len() >= values.len()
            &&& list.subrange(0, values.len() as int) == values
        }),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    let all = list_of_component_values_loop(input, index, stop_token, nested, values).0;
    if is(item, Token::Eof) || is_stop(item, stop_token) {
        assert(values.subrange(0, values.len() as int) =~= values);
    } else if is(item, Token::CloseCurly) {
        if nested {
            assert(values.subrange(0, values.len() as int) =~= values);
        } else {
            let (token, next) = consume_a_token(input, index);
            lemma_list_keeps(input, next, stop_token, nested, values.push(token));
            assert(all.subrange(0, values.len() as int) =~= values.push(token).subrange(
                0,
                values.len() as int,
            ));
        }
    } else {
        let (value, next) = consume_a_component_value(input, index);
        lemma_list_keeps(input, moved(index, next), stop_token, nested, values.push(value));
        assert(all.subrange(0, values.len() as int) =~= values.push(value).subrange(
            0,
            values.len() as int,
        ));
    }
}

/// A `{` after a value: whatever follows, the declaration's list has both.
proof fn lemma_early_exit(
    input: TokenStream,
    index: int,
    nested: bool,
    values: Seq<ComponentValue>,
    x: int,
)
    requires
        0 <= x < values.len(),
        !is_whitespace_token(values[x]),
        is(next_token(input, index), Token::OpenCurly),
    ensures
        has_curly_block_and_another(
            trimmed(
                list_of_component_values_loop(
                    input,
                    index,
                    Some(Token::Semicolon),
                    nested,
                    values,
                ).0,
            ),
        ),
{
    let stop = Some(Token::Semicolon);
    let n = values.len() as int;
    let list = list_of_component_values_loop(input, index, stop, nested, values).0;
    let (block, next) = consume_a_component_value(input, index);
    super::termination::lemma_component_value_advances(input, index);
    lemma_list_keeps(input, moved(index, next), stop, nested, values.push(block));
    lemma_block_shape(
        input,
        discard_a_token(input, index),
        Token::CloseCurly,
        Token::OpenCurly,
        Seq::empty(),
    );
    assert(list[n] == values.push(block).subrange(0, n + 1)[n]);
    assert(list[x] == values[x]) by {
        assert(values.push(block).subrange(0, n + 1)[x] == values[x]);
    }
    assert(is_curly_block(list[n]));
    lemma_block_and_another(list, x, n);
}

/// [`has_curly_block`] of a list with one more item.
proof fn lemma_push_curly(values: Seq<ComponentValue>, value: ComponentValue, i: int)
    requires
        0 <= i <= values.len(),
    ensures
        has_curly_block(values.push(value), i) == (has_curly_block(values, i) || is_curly_block(
            value,
        )),
    decreases values.len() - i,
{
    if i < values.len() {
        lemma_push_curly(values, value, i + 1);
        assert(values.push(value)[i] == values[i]);
    } else {
        assert(values.push(value)[i] == value);
        assert(!has_curly_block(values.push(value), i + 1));
    }
}

/// [`non_whitespace_count`] of a list with one more item.
proof fn lemma_push_count(values: Seq<ComponentValue>, value: ComponentValue, i: int)
    requires
        0 <= i <= values.len(),
    ensures
        non_whitespace_count(values.push(value), i) == non_whitespace_count(values, i) + if is_whitespace_token(value) {
            0nat
        } else {
            1nat
        },
    decreases values.len() - i,
{
    if i < values.len() {
        lemma_push_count(values, value, i + 1);
        assert(values.push(value)[i] == values[i]);
    } else {
        assert(values.push(value)[i] == value);
        assert(non_whitespace_count(values.push(value), i + 1) == 0);
    }
}

// ------------------------------------------------------------------------------------
// The marks
// ------------------------------------------------------------------------------------

/// A place in a value being read, just after a non-whitespace item.
#[derive(Clone, Copy)]
pub struct Mark {
    /// The position after it.
    pub pos: usize,
    /// The row after it.
    pub h: usize,
    /// True if the value up to here has a `{}` block.
    pub curly: bool,
    /// How many non-whitespace values it has, up to 2.
    pub count: u8,
    /// The [`item_kind`] of the item before it.
    pub last: u8,
}

/// What the spec knows of a [`Mark`].
pub ghost struct GhostMark {
    /// How many items of the list are before it.
    pub m: int,
    /// The stream's index there.
    pub i: int,
}

/// What step 6 wants to know of an item: 1 for a `<delim-token>` "!", 2 for an
/// `<ident-token>` "important", and otherwise 0.
pub open spec fn item_kind(value: ComponentValue) -> u8 {
    if is(value, Token::Delim { value: 0x21 }) {
        1
    } else if is_ident(value) && ascii_case_insensitive_match(
        token_value(value),
        important_string(),
    ) {
        2
    } else {
        0
    }
}

/// The [`item_kind`] of the last of the first `m` items.
pub open spec fn last_kind(list: Seq<ComponentValue>, m: int) -> u8 {
    if m <= 0 {
        0
    } else {
        item_kind(list[m - 1])
    }
}

/// `count`, up to 2.
pub open spec fn capped(count: nat) -> u8 {
    if count >= 2 {
        2
    } else {
        count as u8
    }
}

/// True if `e` is the place `g` of `list`.
pub open spec fn mark_ok(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    lo: int,
    start: int,
    list: Seq<ComponentValue>,
    e: Mark,
    g: GhostMark,
) -> bool {
    &&& 0 <= g.m <= list.len()
    &&& lo <= e.h <= rows.len()
    &&& view_list(text, false, rows, lo, e.h as int) == list.subrange(0, g.m)
    &&& at_index(text, false, g.i, e.pos as int)
    &&& e.pos <= text.len()
    &&& (g.m == 0) == (e.h == lo)
    &&& g.m == 0 ==> g.i == start
    &&& g.m > 0 ==> g.i > start
    &&& e.last == last_kind(list, g.m)
    &&& e.curly == has_curly_block(list.subrange(0, g.m), 0)
    &&& e.count == capped(non_whitespace_count(list.subrange(0, g.m), 0))
}

/// The invariant of the value's loop.
#[verifier::opaque]
pub open spec fn marks_ok(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
) -> bool {
    let list = view_list(text, false, rows, lo, rows.len() as int);
    let n = list.len() as int;
    &&& mark_ok(text, rows, lo, start, list, e.0, g.0)
    &&& mark_ok(text, rows, lo, start, list, e.1, g.1)
    &&& mark_ok(text, rows, lo, start, list, e.2, g.2)
    &&& g.0.m - 1 == last_non_whitespace(list, n)
    &&& g.1.m - 1 == last_non_whitespace(list, g.0.m - 1)
    &&& g.2.m - 1 == last_non_whitespace(list, g.1.m - 1)
    &&& index - g.0.i == n - g.0.m
    &&& single.0 ==> g.0.i - g.1.i == g.0.m - g.1.m
    &&& single.1 ==> g.1.i - g.2.i == g.1.m - g.2.m
    &&& !single.0 ==> g.0.m > 0 && !(list[g.0.m - 1] is Token)
    &&& !single.1 ==> g.1.m > 0 && !(list[g.1.m - 1] is Token)
}

/// A mark stays what it was when the list and the rows grow.
proof fn lemma_mark_grows(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    lo: int,
    start: int,
    list: Seq<ComponentValue>,
    value: ComponentValue,
    e: Mark,
    g: GhostMark,
)
    requires
        mark_ok(text, rows, lo, start, list, e, g),
        extends(rows, new),
        rows.len() <= new.len(),
    ensures
        mark_ok(text, new, lo, start, list.push(value), e, g),
{
    lemma_agree_list(text, false, rows, new, lo, e.h as int);
    assert(list.push(value).subrange(0, g.m) =~= list.subrange(0, g.m));
    if g.m > 0 {
        assert(list.push(value)[g.m - 1] == list[g.m - 1]);
    }
}

/// [`last_non_whitespace`] below the end of a list does not see what is pushed.
proof fn lemma_lnw_push(list: Seq<ComponentValue>, value: ComponentValue, end: int)
    requires
        end <= list.len(),
    ensures
        last_non_whitespace(list.push(value), end) == last_non_whitespace(list, end),
    decreases end,
{
    if end > 0 {
        assert(list.push(value)[end - 1] == list[end - 1]);
        lemma_lnw_push(list, value, end - 1);
    }
}

/// The marks when a value starts.
proof fn lemma_marks_start(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    start: int,
    e: Mark,
)
    requires
        at_index(text, false, start, e.pos as int),
        e.pos <= text.len(),
        e.h == rows.len(),
        !e.curly,
        e.count == 0,
        e.last == 0,
    ensures
        marks_ok(
            text,
            rows,
            rows.len() as int,
            start,
            start,
            (e, e, e),
            (
                GhostMark { m: 0, i: start },
                GhostMark { m: 0, i: start },
                GhostMark { m: 0, i: start },
            ),
            (true, true),
        ),
{
    reveal(marks_ok);
    let lo = rows.len() as int;
    let list = view_list(text, false, rows, lo, lo);
    assert(list =~= Seq::<ComponentValue>::empty());
    assert(list.subrange(0, 0) =~= Seq::<ComponentValue>::empty());
    assert(!has_curly_block(list.subrange(0, 0), 0));
    assert(non_whitespace_count(list.subrange(0, 0), 0) == 0);
    assert(capped(0) == 0);
}

/// A whitespace token changes nothing but the index.
proof fn lemma_marks_whitespace(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
)
    requires
        marks_ok(text, rows, lo, start, index, e, g, single),
        extends(rows, new),
        rows.len() < new.len(),
        view_list(text, false, new, lo, new.len() as int) == view_list(
            text,
            false,
            rows,
            lo,
            rows.len() as int,
        ).push(ComponentValue::Token { token: Token::Whitespace }),
    ensures
        marks_ok(text, new, lo, start, index + 1, e, g, single),
{
    reveal(marks_ok);
    let list = view_list(text, false, rows, lo, rows.len() as int);
    let value = ComponentValue::Token { token: Token::Whitespace };
    let bigger = list.push(value);
    let n = list.len() as int;
    lemma_mark_grows(text, rows, new, lo, start, list, value, e.0, g.0);
    lemma_mark_grows(text, rows, new, lo, start, list, value, e.1, g.1);
    lemma_mark_grows(text, rows, new, lo, start, list, value, e.2, g.2);
    lemma_lnw_push(list, value, n);
    assert(bigger[n] == value);
    assert(last_non_whitespace(bigger, n + 1) == last_non_whitespace(bigger, n));
    lemma_lnw(list, n);
    lemma_lnw_push(list, value, g.0.m - 1);
    lemma_lnw_push(list, value, g.1.m - 1);
    if !single.0 {
        assert(bigger[g.0.m - 1] == list[g.0.m - 1]);
    }
    if !single.1 {
        assert(bigger[g.1.m - 1] == list[g.1.m - 1]);
    }
}

/// A non-whitespace item moves every mark along. `single` says it took one token.
proof fn lemma_marks_item(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
    value: ComponentValue,
    after: int,
    first: Mark,
    is_single: bool,
)
    requires
        marks_ok(text, rows, lo, start, index, e, g, single),
        extends(rows, new),
        rows.len() < new.len(),
        !is_whitespace_token(value),
        view_list(text, false, new, lo, new.len() as int) == view_list(
            text,
            false,
            rows,
            lo,
            rows.len() as int,
        ).push(value),
        at_index(text, false, after, first.pos as int),
        first.pos <= text.len(),
        first.h == new.len(),
        first.curly == has_curly_block(
            view_list(text, false, new, lo, new.len() as int),
            0,
        ),
        first.count == capped(
            non_whitespace_count(view_list(text, false, new, lo, new.len() as int), 0),
        ),
        is_single ==> after == index + 1,
        !is_single ==> !(value is Token),
        after > start,
        first.last == item_kind(value),
    ensures
        marks_ok(
            text,
            new,
            lo,
            start,
            after,
            (first, e.0, e.1),
            (GhostMark { m: view_list(text, false, new, lo, new.len() as int).len() as int, i: after }, g.0, g.1),
            (is_single, single.0),
        ),
{
    reveal(marks_ok);
    let list = view_list(text, false, rows, lo, rows.len() as int);
    let bigger = list.push(value);
    let n = list.len() as int;
    assert(view_list(text, false, new, lo, new.len() as int) == bigger);
    lemma_mark_grows(text, rows, new, lo, start, list, value, e.0, g.0);
    lemma_mark_grows(text, rows, new, lo, start, list, value, e.1, g.1);
    assert(bigger.subrange(0, n + 1) =~= bigger);
    assert(bigger[n] == value);
    assert(last_non_whitespace(bigger, n + 1) == n);
    lemma_lnw_push(list, value, n);
    lemma_lnw_push(list, value, g.0.m - 1);
    if !single.0 {
        assert(bigger[g.0.m - 1] == list[g.0.m - 1]);
    }
    assert((lo == first.h as int) == false) by {
        assert(lo <= rows.len());
    }
}

/// A mark that has moved is after a non-whitespace item.
proof fn lemma_marks_nonempty(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
)
    requires
        marks_ok(text, rows, lo, start, index, e, g, single),
        e.0.h != lo,
    ensures
        ({
            let list = view_list(text, false, rows, lo, rows.len() as int);
            &&& 0 < g.0.m <= list.len()
            &&& !is_whitespace_token(list[g.0.m - 1])
        }),
{
    reveal(marks_ok);
    let list = view_list(text, false, rows, lo, rows.len() as int);
    lemma_lnw(list, list.len() as int);
}

/// Cutting rows off the end leaves the values before the cut.
pub proof fn lemma_cut(
    text: Seq<u32>,
    flag: bool,
    old: Seq<ExecRow>,
    whole: Seq<ExecRow>,
    cut: Seq<ExecRow>,
    lo: int,
    h: int,
)
    requires
        extends(old, whole),
        old.len() <= h <= whole.len(),
        0 <= lo,
        cut == whole.subrange(0, h),
    ensures
        extends(old, cut),
        view_list(text, flag, cut, lo, h) == view_list(text, flag, whole, lo, h),
{
    assert forall|k: int| 0 <= k < old.len() implies old[k] == cut[k] by {
        assert(old[k] == whole[k]);
    }
    assert forall|k: int| 0 <= k < h implies whole[k] == cut[k] by {}
    lemma_agree_list(text, flag, whole, cut, lo, h);
}

/// What the marks say once the list is whole.
proof fn lemma_marks_end(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
)
    requires
        marks_ok(text, rows, lo, start, index, e, g, single),
    ensures
        ({
            let list = view_list(text, false, rows, lo, rows.len() as int);
            let n = list.len() as int;
            let kept = if important_at(list) is Some {
                g.2
            } else {
                g.0
            };
            let mark = if important_at(list) is Some {
                e.2
            } else {
                e.0
            };
            &&& mark_ok(text, rows, lo, start, list, mark, kept)
            &&& trimmed(list) == list.subrange(0, kept.m)
            &&& index - (n - trimmed(list).len()) == kept.i
        }),
{
    reveal(marks_ok);
    let list = view_list(text, false, rows, lo, rows.len() as int);
    let n = list.len() as int;
    lemma_trimmed(list);
    lemma_lnw(list, n);
    match important_at(list) {
        Some((a, b)) => {
            assert(b == g.0.m - 1);
            assert(a == g.1.m - 1);
            assert(list[b] is Token);
            assert(list[a] is Token);
            assert(single.0);
            assert(single.1);
            assert(kept_items(list) == g.2.m);
        },
        None => {
            assert(kept_items(list) == g.0.m);
        },
    }
}

/// True if the marks' last two items are "!" and "important": step 6.
proof fn lemma_is_important(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    lo: int,
    start: int,
    index: int,
    e: (Mark, Mark, Mark),
    g: (GhostMark, GhostMark, GhostMark),
    single: (bool, bool),
)
    requires
        marks_ok(text, rows, lo, start, index, e, g, single),
    ensures
        (e.0.last == 2 && e.1.last == 1) == (important_at(
            view_list(text, false, rows, lo, rows.len() as int),
        ) is Some),
{
    reveal(marks_ok);
    let list = view_list(text, false, rows, lo, rows.len() as int);
    lemma_lnw(list, list.len() as int);
    lemma_lnw(list, g.0.m - 1);
}

/// ASCII lowercase.
fn lowercase(c: u32) -> (r: u32)
    ensures
        r == ascii_lowercase(c),
{
    if 0x41 <= c && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

/// True if `string` is an ASCII case-insensitive match for `target`.
fn matches_ignoring_case(string: &Vec<u32>, target: &[u32]) -> (r: bool)
    ensures
        r == ascii_case_insensitive_match(string@, target@),
{
    if string.len() != target.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < string.len()
        invariant
            i <= string.len(),
            string.len() == target.len(),
            matches_from(string@, target@, 0) == matches_from(string@, target@, i as int),
        decreases string.len() - i,
    {
        if lowercase(string[i]) != target[i] {
            proof {
                lemma_mismatch(string@, target@, 0, i as int);
            }
            return false;
        }
        proof {
            lemma_match_step(string@, target@, i as int);
        }
        i = i + 1;
    }
    true
}

/// [`matches_from`] moves one along a match.
proof fn lemma_match_step(string: Seq<u32>, target: Seq<u32>, i: int)
    requires
        0 <= i < string.len(),
        ascii_lowercase(string[i]) == target[i],
    ensures
        matches_from(string, target, i) == matches_from(string, target, i + 1),
{
}

/// [`matches_from`] is false before a mismatch.
proof fn lemma_mismatch(string: Seq<u32>, target: Seq<u32>, i: int, k: int)
    requires
        0 <= i <= k < string.len(),
        ascii_lowercase(string[k]) != target[k],
    ensures
        !matches_from(string, target, i),
    decreases k - i,
{
    if i < k {
        lemma_mismatch(string, target, i + 1, k);
    }
}

/// True if `value` is an "important", as a number for a mark.
fn is_important_word(value: &Vec<u32>) -> (r: bool)
    ensures
        r == ascii_case_insensitive_match(value@, important_string()),
{
    let word: [u32; 9] = [0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61, 0x6E, 0x74];
    proof {
        assert(word@ =~= important_string());
    }
    matches_ignoring_case(value, word.as_slice())
}

/// [`item_kind`] of a token.
fn kind_of(token: &ExecToken) -> (r: u8)
    ensures
        r == item_kind(
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ),
{
    match token {
        ExecToken::Delim { value } => if *value == 0x21 {
            1
        } else {
            0
        },
        ExecToken::Ident { value } => if is_important_word(value) {
            2
        } else {
            0
        },
        _ => 0,
    }
}

/// True if `name` is "unicode-range", ASCII case-insensitively.
fn is_unicode_range_name(name: &Vec<u32>) -> (r: bool)
    ensures
        r == ascii_case_insensitive_match(name@, unicode_range_string()),
{
    let word: [u32; 13] = [
        0x75, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65, 0x2D, 0x72, 0x61, 0x6E, 0x67, 0x65,
    ];
    proof {
        assert(word@ =~= unicode_range_string());
    }
    matches_ignoring_case(name, word.as_slice())
}

/// True if `name` is a custom property name string.
fn is_custom_name(name: &Vec<u32>) -> (r: bool)
    ensures
        r == is_custom_property_name_string(name@),
{
    name.len() >= 2 && name[0] == 0x2D && name[1] == 0x2D
}

/// What the row of a value read from `token` says it is.
pub proof fn lemma_value_kind(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    k: int,
    token: Token,
)
    requires
        0 <= k < rows.len(),
        token_at(text, false, rows[k].pos as int) == token,
    ensures
        is_curly_block(view_value(text, false, rows, k)) == (token is OpenCurly),
        opens_a_value(token) ==> !(view_value(text, false, rows, k) is Token),
        opens_a_value(token) ==> item_kind(view_value(text, false, rows, k)) == 0,
        !opens_a_value(token) ==> view_value(text, false, rows, k) == (ComponentValue::Token {
            token,
        }),
{
}

/// How rows may grow: `room` is what is left for them.
pub open spec fn room(text: Seq<u32>, rows: nat, index: int, pos: int) -> bool {
    rows + tokens_left(text, false, index) + (text.len() - pos) + 1 <= u32::MAX
}

/// A slice of the text, for a unicode-range value.
fn copy_of(text: &[u32], from: usize, to: usize) -> (r: Vec<u32>)
    requires
        from <= to <= text.len(),
    ensures
        r@ == text@.subrange(from as int, to as int),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i = from;
    while i < to
        invariant
            from <= i <= to <= text.len(),
            out@ == text@.subrange(from as int, i as int),
        decreases to - i,
    {
        out.push(text[i]);
        i = i + 1;
        proof {
            assert(out@ =~= text@.subrange(from as int, i as int));
        }
    }
    out
}

/// The last step of a value: `value` and the index it ends at.
pub open spec fn declaration_result(
    input: TokenStream,
    start: int,
    nested: bool,
    name: Seq<u32>,
) -> (Option<Declaration>, int) {
    declaration_value(input, start, nested, name)
}

/// Steps 5 to 9 of "consume a declaration".
fn read_declaration_value(
    text: &[u32],
    pos: usize,
    nested: bool,
    attempt: bool,
    custom: bool,
    unicode: bool,
    name_pos: usize,
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    Ghost(start): Ghost<int>,
    Ghost(name): Ghost<Seq<u32>>,
) -> (r: (bool, usize, Ghost<int>))
    requires
        text_requires(text@),
        at_index(text@, false, start, pos as int),
        pos <= text.len(),
        name_pos <= text.len(),
        room(text@, old(rows).len() as nat, start, pos as int),
        old(decls).len() < u32::MAX,
        custom == is_custom_property_name_string(name),
        unicode == ascii_case_insensitive_match(name, unicode_range_string()),
        token_value(
            ComponentValue::Token { token: token_at(text@, false, name_pos as int) },
        ) == name,
    ensures
        ({
            let (decl, after) = declaration_value(stream_of(text@, false), start, nested, name);
            &&& r.0 == (decl is Some)
            &&& r.0 ==> final(decls).len() == old(decls).len() + 1
            &&& r.0 ==> final(decls)@.drop_last() == old(decls)@
            &&& r.0 ==> view_declaration(text@, final(rows)@, final(decls)@.last()) == decl.unwrap()
            &&& r.0 ==> final(decls)@.last().value_hi == final(rows).len()
            &&& r.0 ==> final(decls)@.last().value_lo == old(rows).len()
            &&& r.0 ==> old(rows).len() <= final(rows).len()
            &&& r.0 ==> extends(old(rows)@, final(rows)@)
            &&& !r.0 ==> final(rows)@ == old(rows)@
            &&& !r.0 ==> final(decls)@ == old(decls)@
            &&& (r.0 || !attempt) ==> r.2@ == after
            &&& (r.0 || !attempt) ==> at_index(text@, false, after, r.1 as int)
            &&& (r.0 || !attempt) ==> pos <= r.1 <= text.len()
            &&& (r.0 || !attempt) ==> after >= start
            &&& (r.0 || !attempt) ==> room(text@, final(rows).len() as nat, after, r.1 as int)
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost target = consume_a_list_of_component_values(
        input,
        start,
        Some(Token::Semicolon),
        nested,
    );
    let ghost old_rows = rows@;
    let lo = rows.len();
    let mut at = pos;
    let ghost mut idx = start;
    let mark = Mark { pos, h: lo, curly: false, count: 0, last: 0 };
    let mut e = (mark, mark, mark);
    let ghost mut g = (
        GhostMark { m: 0, i: start },
        GhostMark { m: 0, i: start },
        GhostMark { m: 0, i: start },
    );
    let ghost mut single = (true, true);
    let mut run_curly = false;
    let mut run_count: u8 = 0;
    let mut read_any = false;
    proof {
        lemma_marks_start(text@, rows@, start, mark);
        assert(view_list(text@, false, rows@, lo as int, lo as int)
            =~= Seq::<ComponentValue>::empty());
        assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {}
    }
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, false),
            at_index(text@, false, idx, at as int),
            pos <= at <= text.len(),
            start <= idx,
            lo == old_rows.len(),
            old_rows == old(rows)@,
            extends(old_rows, rows@),
            lo <= rows.len(),
            paid(text@, false, lo as nat, start, rows.len() as nat, idx),
            room(text@, lo as nat, start, pos as int),
            marks_ok(text@, rows@, lo as int, start, idx, e, g, single),
            run_curly == has_curly_block(
                view_list(text@, false, rows@, lo as int, rows.len() as int),
                0,
            ),
            run_count == capped(
                non_whitespace_count(
                    view_list(text@, false, rows@, lo as int, rows.len() as int),
                    0,
                ),
            ),
            list_of_component_values_loop(
                input,
                idx,
                Some(Token::Semicolon),
                nested,
                view_list(text@, false, rows@, lo as int, rows.len() as int),
            ) == target,
            target == consume_a_list_of_component_values(
                input,
                start,
                Some(Token::Semicolon),
                nested,
            ),
            idx > start ==> at >= input.source.unwrap().spans[start].end,
            read_any == (idx > start),
            custom == is_custom_property_name_string(name),
        ensures
            is(next_token(input, idx), Token::Eof) || is(next_token(input, idx), Token::Semicolon)
                || (nested && is(next_token(input, idx), Token::CloseCurly)),
        decreases tokens_left(text@, false, idx),
    {
        let ghost values = view_list(text@, false, rows@, lo as int, rows.len() as int);
        let ghost before = rows@;
        let ghost before_idx = idx;
        let ghost before_e = e;
        let ghost before_g = g;
        let ghost before_single = single;
        let (token, next) = read_token(text, false, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Eof) || matches!(token, ExecToken::Semicolon) {
            break;
        }
        if nested && matches!(token, ExecToken::CloseCurly) {
            break;
        }
        if matches!(token, ExecToken::Whitespace) {
            let start_row = rows.len() as u32;
            let row = ExecRow { pos: at as u32, start: start_row };
            rows.push(row);
            proof {
                lemma_token_added(text@, false, before, lo as int, at as u32, token_view);
                lemma_extends_chain(old_rows, before, rows@);
                lemma_marks_whitespace(
                    text@,
                    before,
                    rows@,
                    lo as int,
                    start,
                    idx,
                    e,
                    g,
                    single,
                );
                lemma_push_curly(values, ComponentValue::Token { token: token_view }, 0);
                lemma_push_count(values, ComponentValue::Token { token: token_view }, 0);
                super::termination::lemma_component_value_advances(input, idx);
                idx = idx + 1;
            }
            at = next;
            read_any = true;
        } else {
            let is_curly = matches!(token, ExecToken::OpenCurly);
            if attempt && !custom && is_curly && e.0.h != lo {
                rows.truncate(lo);
                proof {
                    lemma_marks_nonempty(
                        text@,
                        before,
                        lo as int,
                        start,
                        idx,
                        e,
                        g,
                        single,
                    );
                    lemma_early_exit(input, idx, nested, values, g.0.m - 1);
                    assert(rows@ =~= old_rows);
                    assert(declaration_value(input, start, nested, name).0 is None);
                }
                return (false, pos, Ghost(start));
            }
            let kind = kind_of(&token);
            let leaf = !opens(&token);
            let end = if matches!(token, ExecToken::CloseCurly) {
                let start_row = rows.len() as u32;
                rows.push(ExecRow { pos: at as u32, start: start_row });
                next
            } else {
                read_component_value(text, false, token, at, next, rows, Ghost(idx))
            };
            run_curly = run_curly || is_curly;
            run_count = if run_count >= 2 {
                2
            } else {
                run_count + 1
            };
            let first = Mark { pos: end, h: rows.len(), curly: run_curly, count: run_count, last: kind };
            proof {
                super::termination::lemma_component_value_advances(input, idx);
                let (value, after) = if token_view is CloseCurly {
                    consume_a_token(input, idx)
                } else {
                    consume_a_component_value(input, idx)
                };
                if token_view is CloseCurly {
                    lemma_token_added(text@, false, before, lo as int, at as u32, token_view);
                } else {
                    lemma_value_added(text@, false, before, rows@, lo as int, value);
                }
                assert(rows@[rows.len() - 1].pos == at as u32) by {
                    assert(rows@.last() == rows@[rows.len() - 1]);
                }
                lemma_extends_chain(old_rows, before, rows@);
                lemma_value_kind(text@, rows@, rows.len() - 1, token_view);
                lemma_push_curly(values, value, 0);
                lemma_push_count(values, value, 0);
                lemma_marks_item(
                    text@,
                    before,
                    rows@,
                    lo as int,
                    start,
                    idx,
                    before_e,
                    before_g,
                    before_single,
                    value,
                    after,
                    first,
                    leaf,
                );
                g = (
                    GhostMark {
                        m: view_list(text@, false, rows@, lo as int, rows.len() as int).len() as int,
                        i: after,
                    },
                    before_g.0,
                    before_g.1,
                );
                single = (leaf, before_single.0);
                idx = after;
            }
            e = (first, e.0, e.1);
            at = end;
            read_any = true;
        }
    }
    let ghost list = view_list(text@, false, rows@, lo as int, rows.len() as int);
    let important = e.0.last == 2 && e.1.last == 1;
    let kept = if important {
        e.2
    } else {
        e.0
    };
    proof {
        lemma_is_important(text@, rows@, lo as int, start, idx, e, g, single);
        lemma_marks_end(text@, rows@, lo as int, start, idx, e, g, single);
        assert(target == (list, idx));
    }
    if custom {
        let (text_start, text_end) = if kept.h == lo {
            (0usize, 0usize)
        } else {
            (crate::tokenizer::exec::read_comments(text, pos), kept.pos)
        };
        let ghost whole = rows@;
        rows.truncate(kept.h);
        decls.push(
            ExecDeclaration {
                name_pos: name_pos as u32,
                value_lo: lo as u32,
                value_hi: kept.h as u32,
                important,
                kind: ExecDeclarationKind::Custom,
                text_start: text_start as u32,
                text_end: text_end as u32,
            },
        );
        proof {
            lemma_cut(text@, false, old_rows, whole, rows@, lo as int, kept.h as int);
            super::lemmas::lemma_span_start(text@, false, start);
            assert(text@.subrange(0, 0) =~= Seq::<u32>::empty());
        }
        return (true, at, Ghost(idx));
    }
    if kept.curly && kept.count >= 2 {
        rows.truncate(lo);
        proof {
            assert(rows@ =~= old_rows);
        }
        return (false, at, Ghost(idx));
    }
    if unicode {
        let (text_start, text_end) = if read_any {
            (crate::tokenizer::exec::read_comments(text, pos), at)
        } else {
            (0usize, 0usize)
        };
        proof {
            super::lemmas::theorem_reader(text@, false);
            assert(super::contract::reader_matches(text@, false, start));
            crate::tokenizer::termination::lemma_token_advances(text@, pos as int, false);
        }
        let ghost whole = rows@;
        rows.truncate(lo);
        let ghost cut = rows@;
        proof {
            lemma_cut(text@, false, old_rows, whole, cut, lo as int, lo as int);
            assert(cut =~= old_rows);
        }
        let part = copy_of(text, text_start, text_end);
        proof {
            lemma_at_start(part@, true);
            crate::tokenizer::lemmas::lemma_loop_bounded(part@, 0, true, Seq::empty());
        }
        let read = read_list(part.as_slice(), true, 0, 0, false, rows, Ghost(0));
        decls.push(
            ExecDeclaration {
                name_pos: name_pos as u32,
                value_lo: lo as u32,
                value_hi: rows.len() as u32,
                important,
                kind: ExecDeclarationKind::UnicodeRange,
                text_start: text_start as u32,
                text_end: text_end as u32,
            },
        );
        proof {
            let seg = part@;
            let stream = stream_of(seg, true);
            super::lemmas::lemma_span_start(text@, false, start);
            assert(stop_token(0) == None::<Token>);
            if read_any {
                assert(input.source.unwrap().spans[idx - 1].end == at as int);
                assert(segment(input, start, idx) == Some(seg));
            } else {
                assert(seg =~= Seq::<u32>::empty());
                assert(segment(input, start, idx) == Some(seg));
            }
            assert(text@.subrange(text_start as int, text_end as int) == seg);
            assert(view_list(seg, true, rows@, lo as int, rows.len() as int)
                == consume_the_value_of_a_unicode_range_descriptor(seg));
            // Rows: what the segment added is paid for by its tokens, and it has no more
            // than one for each code point, and the EOF token, which adds no row.
            assert(read.1@ < stream.tokens.len());
            assert(stream.tokens.len() <= seg.len() + 1);
            assert(rows.len() <= lo + read.1@);
            assert(seg.len() <= at - pos);
            assert(tokens_left(text@, false, idx) <= tokens_left(text@, false, start));
        }
        return (true, at, Ghost(idx));
    }
    let ghost whole = rows@;
    rows.truncate(kept.h);
    decls.push(
        ExecDeclaration {
            name_pos: name_pos as u32,
            value_lo: lo as u32,
            value_hi: kept.h as u32,
            important,
            kind: ExecDeclarationKind::Plain,
            text_start: 0,
            text_end: 0,
        },
    );
    proof {
        lemma_cut(text@, false, old_rows, whole, rows@, lo as int, kept.h as int);
    }
    (true, at, Ghost(idx))
}

/// "Consume a declaration". With `attempt`, the caller goes back on failure, so a failure
/// reads no remnants and says nothing of where it ended.
pub fn read_declaration(
    text: &[u32],
    pos: usize,
    nested: bool,
    attempt: bool,
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    Ghost(index): Ghost<int>,
) -> (r: (bool, usize, Ghost<int>))
    requires
        text_requires(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        room(text@, old(rows).len() as nat, index, pos as int),
        old(decls).len() < u32::MAX,
    ensures
        ({
            let (decl, after) = consume_a_declaration(stream_of(text@, false), index, nested);
            &&& r.0 == (decl is Some)
            &&& r.0 ==> final(decls).len() == old(decls).len() + 1
            &&& r.0 ==> final(decls)@.drop_last() == old(decls)@
            &&& r.0 ==> view_declaration(text@, final(rows)@, final(decls)@.last()) == decl.unwrap()
            &&& r.0 ==> final(decls)@.last().value_hi == final(rows).len()
            &&& r.0 ==> final(decls)@.last().value_lo == old(rows).len()
            &&& r.0 ==> old(rows).len() <= final(rows).len()
            &&& r.0 ==> extends(old(rows)@, final(rows)@)
            &&& r.0 ==> after > index
            &&& !r.0 ==> final(rows)@ == old(rows)@
            &&& !r.0 ==> final(decls)@ == old(decls)@
            &&& (r.0 || !attempt) ==> r.2@ == after
            &&& (r.0 || !attempt) ==> at_index(text@, false, after, r.1 as int)
            &&& (r.0 || !attempt) ==> pos <= r.1 <= text.len()
            &&& (r.0 || !attempt) ==> after >= index
            &&& (r.0 || !attempt) ==> room(text@, final(rows).len() as nat, after, r.1 as int)
        }),
{
    let ghost input = stream_of(text@, false);
    let (first, next) = read_token(text, false, pos, Ghost(index));
    let ghost first_view = crate::tokenizer::exec::view_token(first);
    let (is_name, custom, unicode) = match &first {
        ExecToken::Ident { value } => (true, is_custom_name(value), is_unicode_range_name(value)),
        _ => (false, false, false),
    };
    if !is_name {
        if attempt {
            return (false, pos, Ghost(index));
        }
        let (end, after) = read_remnants(text, false, pos, nested, Ghost(index));
        return (false, end, after);
    }
    let ghost name = token_value(ComponentValue::Token { token: first_view });
    let (after_name, Ghost(name_end)) = skip_whitespace(text, false, next, Ghost(index + 1));
    let (colon, after_colon) = read_token(text, false, after_name, Ghost(name_end));
    if !matches!(colon, ExecToken::Colon) {
        if attempt {
            return (false, pos, Ghost(index));
        }
        let (end, after) = read_remnants(text, false, after_name, nested, Ghost(name_end));
        return (false, end, after);
    }
    let (value_pos, Ghost(start)) = skip_whitespace(
        text,
        false,
        after_colon,
        Ghost(name_end + 1),
    );
    read_declaration_value(
        text,
        value_pos,
        nested,
        attempt,
        custom,
        unicode,
        pos,
        rows,
        decls,
        Ghost(start),
        Ghost(name),
    )
}

} // verus!
