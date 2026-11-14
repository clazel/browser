//! The executable parser of component values, proven to meet [`super::contract`]. It reads
//! in lockstep through the tokenizer's `next_token`, so there is no token list: an index of
//! the spec's stream is a position in the text, kept in step by [`at_index`].
//!
//! There is no recursion: a style sheet is what a page chose, and Verus proves no panics,
//! not no stack overflow. [`read_component_value`] keeps an explicit stack, and its ghost
//! twin is a list of [`ValueFrame`]s. [`unwind`] says what the spec's recursion does with
//! them, so each step of the loop is one unfolding of the spec.

pub use super::contract::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The stream of `text`.
pub open spec fn stream_of(text: Seq<u32>, flag: bool) -> TokenStream {
    token_stream(text, flag)
}

/// How many rows can still be needed at `index`: one for each token left.
pub open spec fn tokens_left(text: Seq<u32>, flag: bool, index: int) -> int {
    stream_of(text, flag).tokens.len() - index
}

/// True if a row for each token left still fits a `u32`.
pub open spec fn rows_fit(text: Seq<u32>, flag: bool, rows: nat, index: int) -> bool {
    rows + tokens_left(text, flag, index) <= u32::MAX
}

/// True if `new` rows at `after` are paid for: no more were added than tokens were read.
pub open spec fn paid(
    text: Seq<u32>,
    flag: bool,
    old: nat,
    index: int,
    new: nat,
    after: int,
) -> bool {
    new + tokens_left(text, flag, after) <= old + tokens_left(text, flag, index)
}

/// What is needed of a text to read it.
pub open spec fn text_requires(text: Seq<u32>) -> bool {
    crate::tokenizer::contract::input_requires(text) && text.len() < u32::MAX
}

/// The next token. Past it is the next index, unless it is the EOF token.
pub fn read_token(text: &[u32], flag: bool, pos: usize, Ghost(index): Ghost<int>) -> (r: (
    ExecToken,
    usize,
))
    requires
        text_requires(text@),
        at_index(text@, flag, index, pos as int),
        pos <= text.len(),
    ensures
        next_token(stream_of(text@, flag), index) == (ComponentValue::Token {
            token: crate::tokenizer::exec::view_token(r.0),
        }),
        read_a_token(text@, pos as int, flag) == (
            crate::tokenizer::exec::view_token(r.0),
            r.1 as int,
        ),
        !(crate::tokenizer::exec::view_token(r.0) is Eof) ==> at_index(
            text@,
            flag,
            index + 1,
            r.1 as int,
        ),
        pos <= r.1 <= text.len(),
{
    let r = crate::tokenizer::exec::next_token(text, pos, flag);
    proof {
        super::lemmas::theorem_reader(text@, flag);
        assert(super::contract::reader_matches(text@, flag, index));
        crate::tokenizer::lemmas::lemma_loop_bounded(text@, 0, flag, Seq::empty());
    }
    r
}

/// The reader starts at index 0.
pub proof fn lemma_at_start(text: Seq<u32>, flag: bool)
    ensures
        at_index(text, flag, 0, 0),
{
    crate::tokenizer::lemmas::lemma_loop_bounded(text, 0, flag, Seq::empty());
}

/// True if `token` holds a list of values.
pub fn opens(token: &ExecToken) -> (r: bool)
    ensures
        r == opens_a_value(crate::tokenizer::exec::view_token(*token)),
{
    matches!(
        token,
        ExecToken::Function { .. } | ExecToken::OpenCurly | ExecToken::OpenSquare
            | ExecToken::OpenParen
    )
}

/// What ends a value that `opening` opened: "the mirror variant", or a function's `)`.
pub open spec fn closes(opening: Token) -> Token {
    if opening is Function {
        Token::CloseParen
    } else {
        mirror(ComponentValue::Token { token: opening })
    }
}

/// [`closes`] as a number, for the exec loop to keep: 0 is `}`, 1 is `]` and 2 is `)`.
pub open spec fn ending_token(ending: u8) -> Token {
    if ending == 0 {
        Token::CloseCurly
    } else if ending == 1 {
        Token::CloseSquare
    } else {
        Token::CloseParen
    }
}

/// [`closes`].
fn ending_of(token: &ExecToken) -> (r: u8)
    requires
        opens_a_value(crate::tokenizer::exec::view_token(*token)),
    ensures
        ending_token(r) == closes(crate::tokenizer::exec::view_token(*token)),
{
    match token {
        ExecToken::OpenCurly => 0,
        ExecToken::OpenSquare => 1,
        _ => 2,
    }
}

/// True if `token` is the [`ending_token`] `ending`.
fn is_ending(token: &ExecToken, ending: u8) -> (r: bool)
    ensures
        r == (crate::tokenizer::exec::view_token(*token) == ending_token(ending)),
{
    match token {
        ExecToken::CloseCurly => ending == 0,
        ExecToken::CloseSquare => ending == 1,
        ExecToken::CloseParen => ending != 0 && ending != 1,
        _ => false,
    }
}

/// A value being read: the [`ExecFrame`] of the stack, with what the spec knows of it.
pub ghost struct ValueFrame {
    /// The token that opened it.
    pub opening: Token,
    /// The values read so far.
    pub value: Seq<ComponentValue>,
}

/// One open value.
#[derive(Clone, Copy)]
pub struct ExecFrame {
    /// Where reading gives its opening token.
    pub pos: u32,
    /// The first row inside it.
    pub lo: u32,
}

/// The loop of the spec that reads the inside of a value `opening` opened.
pub open spec fn frame_loop(
    input: TokenStream,
    opening: Token,
    index: int,
    values: Seq<ComponentValue>,
) -> (ComponentValue, int) {
    match opening {
        Token::Function { value } => function_loop(input, index, value, values),
        _ => simple_block_loop(input, index, closes(opening), opening, values),
    }
}

/// What the spec's recursion does once the innermost open value gave `result`: each frame
/// appends what it got and goes on with its loop.
pub open spec fn unwind(
    input: TokenStream,
    frames: Seq<ValueFrame>,
    result: (ComponentValue, int),
) -> (ComponentValue, int)
    decreases frames.len(),
{
    if frames.len() == 0 {
        result
    } else {
        let frame = frames.last();
        unwind(
            input,
            frames.drop_last(),
            frame_loop(input, frame.opening, result.1, frame.value.push(result.0)),
        )
    }
}

/// True if `r1` and `r2` agree on their first `n` rows.
pub open spec fn rows_agree(r1: Seq<ExecRow>, r2: Seq<ExecRow>, n: int) -> bool {
    n <= r1.len() && n <= r2.len() && forall|k: int| 0 <= k < n ==> r1[k] == r2[k]
}

/// [`view_value`] sees only the rows up to and including `k`.
pub proof fn lemma_agree_value(
    text: Seq<u32>,
    flag: bool,
    r1: Seq<ExecRow>,
    r2: Seq<ExecRow>,
    k: int,
)
    requires
        0 <= k,
        rows_agree(r1, r2, k + 1),
    ensures
        view_value(text, flag, r1, k) == view_value(text, flag, r2, k),
    decreases k + 1, 0int,
{
    assert(r1[k] == r2[k]);
    lemma_agree_list(text, flag, r1, r2, r1[k].start as int, k);
}

/// [`view_list`] sees only the rows before `hi`.
pub proof fn lemma_agree_list(
    text: Seq<u32>,
    flag: bool,
    r1: Seq<ExecRow>,
    r2: Seq<ExecRow>,
    lo: int,
    hi: int,
)
    requires
        rows_agree(r1, r2, hi),
    ensures
        view_list(text, flag, r1, lo, hi) == view_list(text, flag, r2, lo, hi),
    decreases hi, 1int,
{
    if lo < 0 || hi <= lo {
    } else {
        assert(r1[hi - 1] == r2[hi - 1]);
        if r1[hi - 1].start < hi {
            lemma_agree_list(text, flag, r1, r2, lo, r1[hi - 1].start as int);
            lemma_agree_value(text, flag, r1, r2, hi - 1);
        }
    }
}

/// Appending a value whose first row is `old.len()` appends it to every list that ends
/// there.
pub proof fn lemma_list_push(
    text: Seq<u32>,
    flag: bool,
    old: Seq<ExecRow>,
    new: Seq<ExecRow>,
    lo: int,
)
    requires
        0 <= lo <= old.len(),
        new.len() > old.len(),
        rows_agree(old, new, old.len() as int),
        new[new.len() - 1].start == old.len(),
        new.len() - 1 >= old.len(),
    ensures
        view_list(text, flag, new, lo, new.len() as int) == view_list(
            text,
            flag,
            old,
            lo,
            old.len() as int,
        ).push(view_value(text, flag, new, new.len() - 1)),
{
    lemma_agree_list(text, flag, old, new, lo, old.len() as int);
}

/// True if the stack and its ghost twin agree with the rows.
pub open spec fn frames_match(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
) -> bool {
    &&& frames.len() == stack.len()
    &&& stack.len() > 0
    &&& forall|j: int|
        #![trigger stack[j]]
        0 <= j < stack.len() ==> stack[j].lo <= rows.len() && token_at(
            text,
            flag,
            stack[j].pos as int,
        ) == frames[j].opening && opens_a_value(frames[j].opening) && stack[j].pos <= text.len()
    &&& forall|j: int|
        #![trigger stack[j]]
        1 <= j < stack.len() ==> stack[j - 1].lo <= stack[j].lo && frames[j - 1].value
            == view_list(text, flag, rows, stack[j - 1].lo as int, stack[j].lo as int)
    &&& frames.last().value == view_list(
        text,
        flag,
        rows,
        stack.last().lo as int,
        rows.len() as int,
    )
}

/// A token that holds nothing goes on the end of the innermost value.
proof fn lemma_leaf_keeps_frames(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    value: ComponentValue,
)
    requires
        frames_match(text, flag, rows, stack, frames),
        new.len() == rows.len() + 1,
        rows_agree(rows, new, rows.len() as int),
        new.last().start == rows.len(),
        view_value(text, flag, new, rows.len() as int) == value,
    ensures
        frames_match(
            text,
            flag,
            new,
            stack,
            frames.update(
                frames.len() - 1,
                ValueFrame { opening: frames.last().opening, value: frames.last().value.push(value) },
            ),
        ),
{
    let top = frames.len() - 1;
    let updated = frames.update(
        top,
        ValueFrame { opening: frames.last().opening, value: frames.last().value.push(value) },
    );
    assert forall|j: int| #![trigger stack[j]] 1 <= j < stack.len() implies stack[j - 1].lo
        <= stack[j].lo && updated[j - 1].value == view_list(
        text,
        flag,
        new,
        stack[j - 1].lo as int,
        stack[j].lo as int,
    ) by {
        assert(stack[j].lo <= rows.len());
        lemma_agree_list(text, flag, rows, new, stack[j - 1].lo as int, stack[j].lo as int);
    }
    assert forall|j: int| #![trigger stack[j]] 0 <= j < stack.len() implies stack[j].lo <= new.len()
        && token_at(text, flag, stack[j].pos as int) == updated[j].opening && opens_a_value(
        updated[j].opening,
    ) && stack[j].pos <= text.len() by {
        assert(stack[j].lo <= rows.len());
    }
    assert(stack.last() == stack[top]);
    assert(stack[top].lo <= rows.len());
    lemma_list_push(text, flag, rows, new, stack.last().lo as int);
}

/// Opening a value adds an empty frame.
proof fn lemma_open_keeps_frames(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    frame: ExecFrame,
    opening: Token,
)
    requires
        frames_match(text, flag, rows, stack, frames),
        frame.lo == rows.len(),
        frame.pos <= text.len(),
        token_at(text, flag, frame.pos as int) == opening,
        opens_a_value(opening),
    ensures
        frames_match(
            text,
            flag,
            rows,
            stack.push(frame),
            frames.push(ValueFrame { opening, value: Seq::empty() }),
        ),
{
    let s2 = stack.push(frame);
    let f2 = frames.push(ValueFrame { opening, value: Seq::empty() });
    assert forall|j: int| #![trigger s2[j]] 0 <= j < s2.len() implies s2[j].lo <= rows.len()
        && token_at(text, flag, s2[j].pos as int) == f2[j].opening && opens_a_value(f2[j].opening)
        && s2[j].pos <= text.len() by {
        if j < stack.len() {
            assert(stack[j] == s2[j]);
        }
    }
    assert forall|j: int| #![trigger s2[j]] 1 <= j < s2.len() implies s2[j - 1].lo <= s2[j].lo
        && f2[j - 1].value == view_list(
        text,
        flag,
        rows,
        s2[j - 1].lo as int,
        s2[j].lo as int,
    ) by {
        assert(s2[j - 1] == stack[j - 1]);
        assert(stack[j - 1].lo <= rows.len());
        if j < stack.len() {
            assert(s2[j] == stack[j]);
        } else {
            assert(stack.last() == stack[j - 1]);
            assert(frames.last() == frames[j - 1]);
        }
    }
    assert(f2.last().value =~= Seq::<ComponentValue>::empty());
}

/// Closing the innermost value with row `new.last()` appends it to the frame around it.
proof fn lemma_close_keeps_frames(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    value: ComponentValue,
)
    requires
        frames_match(text, flag, rows, stack, frames),
        stack.len() >= 2,
        new.len() == rows.len() + 1,
        rows_agree(rows, new, rows.len() as int),
        new.last().start == stack.last().lo,
        view_value(text, flag, new, rows.len() as int) == value,
    ensures
        frames_match(
            text,
            flag,
            new,
            stack.drop_last(),
            frames.drop_last().update(
                frames.len() - 2,
                ValueFrame {
                    opening: frames[frames.len() - 2].opening,
                    value: frames[frames.len() - 2].value.push(value),
                },
            ),
        ),
{
    let n = stack.len() as int;
    let s2 = stack.drop_last();
    let f2 = frames.drop_last().update(
        n - 2,
        ValueFrame { opening: frames[n - 2].opening, value: frames[n - 2].value.push(value) },
    );
    assert forall|j: int| #![trigger s2[j]] 0 <= j < s2.len() implies s2[j].lo <= new.len()
        && token_at(text, flag, s2[j].pos as int) == f2[j].opening && opens_a_value(f2[j].opening)
        && s2[j].pos <= text.len() by {
        assert(s2[j] == stack[j]);
        assert(stack[j].lo <= rows.len());
    }
    assert forall|j: int| #![trigger s2[j]] 1 <= j < s2.len() implies s2[j - 1].lo <= s2[j].lo
        && f2[j - 1].value == view_list(
        text,
        flag,
        new,
        s2[j - 1].lo as int,
        s2[j].lo as int,
    ) by {
        assert(s2[j] == stack[j]);
        assert(s2[j - 1] == stack[j - 1]);
        assert(stack[j].lo <= rows.len());
        lemma_agree_list(text, flag, rows, new, stack[j - 1].lo as int, stack[j].lo as int);
    }
    assert(stack.last() == stack[n - 1]);
    assert(s2.last() == stack[n - 2]);
    assert(stack[n - 1].lo <= rows.len());
    assert(stack[n - 2].lo <= stack[n - 1].lo);
    lemma_agree_list(
        text,
        flag,
        rows,
        new,
        stack[n - 2].lo as int,
        stack[n - 1].lo as int,
    );
    assert(new[new.len() - 1].start == stack[n - 1].lo);
    assert(f2.last().value == frames[n - 2].value.push(value));
}

/// The row of a value that has closed is the value the spec's loop gives.
proof fn lemma_closed_value(
    text: Seq<u32>,
    flag: bool,
    input: TokenStream,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    frame: ExecFrame,
    opening: Token,
    values: Seq<ComponentValue>,
    index: int,
)
    requires
        new.len() == rows.len() + 1,
        rows_agree(rows, new, rows.len() as int),
        new.last() == (ExecRow { pos: frame.pos, start: frame.lo }),
        frame.lo <= rows.len(),
        token_at(text, flag, frame.pos as int) == opening,
        opens_a_value(opening),
        values == view_list(text, flag, rows, frame.lo as int, rows.len() as int),
        is(next_token(input, index), Token::Eof) || is(next_token(input, index), closes(opening)),
    ensures
        view_value(text, flag, new, rows.len() as int) == frame_loop(
            input,
            opening,
            index,
            values,
        ).0,
        frame_loop(input, opening, index, values).1 == discard_a_token(input, index),
{
    lemma_agree_list(text, flag, rows, new, frame.lo as int, rows.len() as int);
    assert(new[rows.len() as int] == new.last());
}

/// An opening token in a value: the value goes on with what the inner one returned.
proof fn lemma_open_step(
    input: TokenStream,
    outer: Token,
    index: int,
    values: Seq<ComponentValue>,
    inner: Token,
)
    requires
        next_token(input, index) == (ComponentValue::Token { token: inner }),
        opens_a_value(inner),
        !(is(next_token(input, index), closes(outer))),
    ensures
        ({
            let r = frame_loop(input, inner, index + 1, Seq::empty());
            &&& frame_loop(input, outer, index, values) == frame_loop(
                input,
                outer,
                r.1,
                values.push(r.0),
            )
            &&& r == consume_a_component_value(input, index)
        }),
{
    super::termination::lemma_component_value_advances(input, index);
    let r = frame_loop(input, inner, index + 1, Seq::empty());
    assert(discard_a_token(input, index) == index + 1);
    assert(r == consume_a_component_value(input, index));
}

/// A token that opens nothing in a value: the value appends it and goes on.
proof fn lemma_leaf_step(
    input: TokenStream,
    outer: Token,
    index: int,
    values: Seq<ComponentValue>,
    token: Token,
)
    requires
        next_token(input, index) == (ComponentValue::Token { token }),
        !opens_a_value(token),
        !(token is Eof),
        !(is(next_token(input, index), closes(outer))),
    ensures
        frame_loop(input, outer, index, values) == frame_loop(
            input,
            outer,
            index + 1,
            values.push(ComponentValue::Token { token }),
        ),
{
    super::termination::lemma_component_value_advances(input, index);
    assert(consume_a_component_value(input, index) == (
        ComponentValue::Token { token },
        index + 1,
    ));
}

/// True if `rows` starts with `old`.
pub open spec fn extends(old: Seq<ExecRow>, rows: Seq<ExecRow>) -> bool {
    rows_agree(old, rows, old.len() as int)
}

/// The invariant of [`read_component_value`]'s loop: the stack matches the rows, and what
/// the spec's recursion does from here is what the whole call must give.
#[verifier::opaque]
pub open spec fn machine(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
) -> bool {
    let input = stream_of(text, flag);
    &&& frames_match(text, flag, rows, stack, frames)
    &&& unwind(
        input,
        frames.drop_last(),
        frame_loop(input, frames.last().opening, index, frames.last().value),
    ) == target
}

/// What the loop reads of [`machine`].
proof fn lemma_machine_top(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
    ensures
        stack.len() == frames.len(),
        stack.len() > 0,
        stack.last().lo <= rows.len(),
        stack.last().pos <= text.len(),
        token_at(text, flag, stack.last().pos as int) == frames.last().opening,
        opens_a_value(frames.last().opening),
{
    reveal(machine);
    assert(stack.last() == stack[stack.len() - 1]);
    assert(frames.last() == frames[frames.len() - 1]);
}

/// The first step: the value `first` opened at `index`.
proof fn lemma_machine_start(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    frame: ExecFrame,
    first: Token,
    index: int,
)
    requires
        frame.lo == rows.len(),
        frame.pos <= text.len(),
        token_at(text, flag, frame.pos as int) == first,
        opens_a_value(first),
        next_token(stream_of(text, flag), index) == (ComponentValue::Token { token: first }),
    ensures
        machine(
            text,
            flag,
            rows,
            seq![frame],
            seq![ValueFrame { opening: first, value: Seq::empty() }],
            index + 1,
            consume_a_component_value(stream_of(text, flag), index),
        ),
{
    reveal(machine);
    let input = stream_of(text, flag);
    let frames = seq![ValueFrame { opening: first, value: Seq::empty() }];
    assert(frames.drop_last() =~= Seq::<ValueFrame>::empty());
    assert(discard_a_token(input, index) == index + 1);
    assert(view_list(text, flag, rows, rows.len() as int, rows.len() as int)
        =~= Seq::<ComponentValue>::empty());
    assert(frames.last() == frames[0]);
    assert(seq![frame].last() == seq![frame][0]);
    assert(frame_loop(input, first, index + 1, Seq::empty()) == consume_a_component_value(
        input,
        index,
    ));
}

/// A token that opens nothing goes on the end of the innermost value.
proof fn lemma_machine_leaf(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
    token: Token,
    pos: u32,
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
        next_token(stream_of(text, flag), index) == (ComponentValue::Token { token }),
        token_at(text, flag, pos as int) == token,
        !opens_a_value(token),
        !(token is Eof),
        !(token == closes(frames.last().opening)),
        new == rows.push(ExecRow { pos, start: rows.len() as u32 }),
        rows.len() < u32::MAX,
    ensures
        machine(
            text,
            flag,
            new,
            stack,
            frames.update(
                frames.len() - 1,
                ValueFrame {
                    opening: frames.last().opening,
                    value: frames.last().value.push(ComponentValue::Token { token }),
                },
            ),
            index + 1,
            target,
        ),
{
    reveal(machine);
    let input = stream_of(text, flag);
    let top = frames.last();
    let value = ComponentValue::Token { token };
    let k = rows.len() as int;
    assert(new[k] == new.last());
    assert(view_value(text, flag, new, k) == value);
    lemma_leaf_keeps_frames(text, flag, rows, new, stack, frames, value);
    lemma_leaf_step(input, top.opening, index, top.value, token);
    let updated = frames.update(
        frames.len() - 1,
        ValueFrame { opening: top.opening, value: top.value.push(value) },
    );
    assert(updated.drop_last() =~= frames.drop_last());
}

/// An opening token adds a frame.
proof fn lemma_machine_open(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
    token: Token,
    frame: ExecFrame,
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
        next_token(stream_of(text, flag), index) == (ComponentValue::Token { token }),
        token_at(text, flag, frame.pos as int) == token,
        opens_a_value(token),
        !(token == closes(frames.last().opening)),
        frame.lo == rows.len(),
        frame.pos <= text.len(),
    ensures
        machine(
            text,
            flag,
            rows,
            stack.push(frame),
            frames.push(ValueFrame { opening: token, value: Seq::empty() }),
            index + 1,
            target,
        ),
{
    reveal(machine);
    let input = stream_of(text, flag);
    let top = frames.last();
    lemma_open_keeps_frames(text, flag, rows, stack, frames, frame, token);
    lemma_open_step(input, top.opening, index, top.value, token);
    let pushed = frames.push(ValueFrame { opening: token, value: Seq::empty() });
    assert(pushed.drop_last() =~= frames);
}

/// The frames after the innermost closes with `value`.
pub open spec fn frames_after_close(
    frames: Seq<ValueFrame>,
    value: ComponentValue,
) -> Seq<ValueFrame> {
    let n = frames.len() as int;
    frames.drop_last().update(
        n - 2,
        ValueFrame { opening: frames[n - 2].opening, value: frames[n - 2].value.push(value) },
    )
}

/// What the innermost value is, when the next token ends it.
pub open spec fn closed_by(
    text: Seq<u32>,
    flag: bool,
    frames: Seq<ValueFrame>,
    index: int,
) -> (ComponentValue, int) {
    frame_loop(stream_of(text, flag), frames.last().opening, index, frames.last().value)
}

/// The innermost value closes and there is one around it.
proof fn lemma_machine_close(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
        is(next_token(stream_of(text, flag), index), Token::Eof) || is(
            next_token(stream_of(text, flag), index),
            closes(frames.last().opening),
        ),
        stack.len() >= 2,
        new == rows.push(ExecRow { pos: stack.last().pos, start: stack.last().lo }),
    ensures
        ({
            let closed = closed_by(text, flag, frames, index);
            &&& closed.1 == discard_a_token(stream_of(text, flag), index)
            &&& machine(
                text,
                flag,
                new,
                stack.drop_last(),
                frames_after_close(frames, closed.0),
                closed.1,
                target,
            )
        }),
{
    reveal(machine);
    let input = stream_of(text, flag);
    let n = frames.len() as int;
    let top = frames.last();
    let closed = closed_by(text, flag, frames, index);
    assert(stack[n - 1] == stack.last());
    assert(frames[n - 1] == top);
    assert(new[rows.len() as int] == new.last());
    lemma_closed_value(
        text,
        flag,
        input,
        rows,
        new,
        ExecFrame { pos: stack.last().pos, lo: stack.last().lo },
        top.opening,
        top.value,
        index,
    );
    lemma_close_keeps_frames(text, flag, rows, new, stack, frames, closed.0);
    let after = frames_after_close(frames, closed.0);
    assert(after.drop_last() =~= frames.drop_last().drop_last());
    assert(frames.drop_last().last() == frames[n - 2]);
    assert(after.last() == after[n - 2]);
}

/// The only value closes, which ends the call.
proof fn lemma_machine_done(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    new: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
        is(next_token(stream_of(text, flag), index), Token::Eof) || is(
            next_token(stream_of(text, flag), index),
            closes(frames.last().opening),
        ),
        stack.len() == 1,
        new == rows.push(ExecRow { pos: stack.last().pos, start: stack.last().lo }),
    ensures
        target.1 == discard_a_token(stream_of(text, flag), index),
        view_value(text, flag, new, rows.len() as int) == target.0,
{
    reveal(machine);
    let input = stream_of(text, flag);
    let top = frames.last();
    assert(stack[0] == stack.last());
    assert(frames[0] == top);
    assert(new[rows.len() as int] == new.last());
    assert(frames.drop_last() =~= Seq::<ValueFrame>::empty());
    lemma_closed_value(
        text,
        flag,
        input,
        rows,
        new,
        ExecFrame { pos: stack.last().pos, lo: stack.last().lo },
        top.opening,
        top.value,
        index,
    );
}

/// The lowest frame stays put, for the rows' first value.
proof fn lemma_machine_bottom(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    stack: Seq<ExecFrame>,
    frames: Seq<ValueFrame>,
    index: int,
    target: (ComponentValue, int),
)
    requires
        machine(text, flag, rows, stack, frames, index, target),
    ensures
        forall|j: int| #![trigger stack[j]] 0 <= j < stack.len() ==> stack[j].lo <= rows.len()
            && stack[j].pos <= text.len(),
{
    reveal(machine);
}

/// Appending a row keeps what [`extends`] says.
proof fn lemma_extends_push(old: Seq<ExecRow>, rows: Seq<ExecRow>, row: ExecRow)
    requires
        extends(old, rows),
    ensures
        extends(old, rows.push(row)),
{
    assert forall|k: int| 0 <= k < old.len() implies old[k] == rows.push(row)[k] by {
        assert(rows[k] == rows.push(row)[k]);
    }
}

/// "Consume a component value", whose first token has been read: `first`, with `next` after
/// it. Its rows go on the end of `rows`, the last of them the value's own.
pub fn read_component_value(
    text: &[u32],
    flag: bool,
    first: ExecToken,
    pos: usize,
    next: usize,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
) -> (end: usize)
    requires
        text_requires(text@),
        at_index(text@, flag, index, pos as int),
        read_a_token(text@, pos as int, flag) == (
            crate::tokenizer::exec::view_token(first),
            next as int,
        ),
        next_token(stream_of(text@, flag), index) == (ComponentValue::Token {
            token: crate::tokenizer::exec::view_token(first),
        }),
        !(crate::tokenizer::exec::view_token(first) is Eof),
        at_index(text@, flag, index + 1, next as int),
        pos <= next <= text.len(),
        rows_fit(text@, flag, old(rows).len() as nat, index),
    ensures
        ({
            let (value, after) = consume_a_component_value(stream_of(text@, flag), index);
            &&& at_index(text@, flag, after, end as int)
            &&& extends(old(rows)@, final(rows)@)
            &&& final(rows).len() > old(rows).len()
            &&& final(rows)@.last().start == old(rows).len()
            &&& view_value(text@, flag, final(rows)@, final(rows).len() - 1) == value
            &&& paid(text@, flag, old(rows).len() as nat, index, final(rows).len() as nat, after)
            &&& after > index
            &&& pos <= end <= text.len()
            &&& final(rows)@.last().pos == pos
            &&& next <= end
        }),
{
    let ghost input = stream_of(text@, flag);
    let ghost old_rows = rows@;
    let ghost target = consume_a_component_value(input, index);
    let ghost first_view = crate::tokenizer::exec::view_token(first);
    proof {
        super::termination::lemma_component_value_advances(input, index);
    }
    if !opens(&first) {
        let start = rows.len() as u32;
        rows.push(ExecRow { pos: pos as u32, start });
        proof {
            let k = old_rows.len() as int;
            lemma_extends_push(old_rows, old_rows, ExecRow { pos: pos as u32, start });
            assert(rows@[k] == rows@.last());
            assert(view_value(text@, flag, rows@, k) == (ComponentValue::Token {
                token: first_view,
            }));
        }
        return next;
    }
    let mut ending = ending_of(&first);
    let mut stack: Vec<ExecFrame> = Vec::new();
    stack.push(ExecFrame { pos: pos as u32, lo: rows.len() as u32 });
    let ghost mut frames: Seq<ValueFrame> = seq![
        ValueFrame { opening: first_view, value: Seq::empty() },
    ];
    let mut at = next;
    let ghost mut idx = index + 1;
    proof {
        assert(stack@ =~= seq![stack@[0]]);
        lemma_machine_start(text@, flag, rows@, stack@[0], first_view, index);
    }
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, flag),
            at_index(text@, flag, idx, at as int),
            at <= text.len(),
            extends(old_rows, rows@),
            machine(text@, flag, rows@, stack@, frames, idx, target),
            stack.len() > 0,
            stack@[0].lo == old_rows.len(),
            rows.len() + stack.len() + tokens_left(text@, flag, idx) <= old_rows.len()
                + tokens_left(text@, flag, index),
            old_rows.len() + tokens_left(text@, flag, index) <= u32::MAX,
            stack@[0].pos == pos,
            pos <= next <= at,
            ending_token(ending) == closes(frames.last().opening),
            target == consume_a_component_value(input, index),
            target.1 > index,
            old_rows.len() <= rows.len(),
            old_rows == old(rows)@,
        decreases 2 * tokens_left(text@, flag, idx) + stack.len(),
    {
        let ghost before_rows = rows@;
        let ghost before_stack = stack@;
        let ghost before_frames = frames;
        let ghost before_idx = idx;
        proof {
            lemma_machine_top(text@, flag, rows@, stack@, frames, idx, target);
        }
        let (token, after) = read_token(text, flag, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Eof) || is_ending(&token, ending) {
            let frame = match stack.pop() {
                Some(frame) => frame,
                None => return at,
            };
            rows.push(ExecRow { pos: frame.pos, start: frame.lo });
            proof {
                lemma_extends_push(old_rows, before_rows, rows@.last());
                assert(before_stack.last() == frame);
            }
            if !matches!(token, ExecToken::Eof) {
                at = after;
            }
            if stack.is_empty() {
                proof {
                    assert(before_stack[0] == frame);
                    lemma_machine_done(
                        text@,
                        flag,
                        before_rows,
                        rows@,
                        before_stack,
                        before_frames,
                        before_idx,
                        target,
                    );
                    assert(target.1 == discard_a_token(input, before_idx));
                    if token_view is Eof {
                        assert(is_empty(input, before_idx));
                        assert(target.1 == before_idx);
                    } else {
                        assert(!is_empty(input, before_idx));
                        assert(target.1 == before_idx + 1);
                    }
                    assert(rows@.last().start == old_rows.len());
                    assert(at_index(text@, flag, target.1, at as int));
                    assert(extends(old_rows, rows@));
                    assert(rows.len() > old_rows.len());
                    assert(view_value(text@, flag, rows@, rows.len() - 1) == target.0);
                    assert(paid(
                        text@,
                        flag,
                        old_rows.len() as nat,
                        index,
                        rows.len() as nat,
                        target.1,
                    ));
                    assert(rows@.last().pos == pos);
                    assert(at <= text.len());
                }
                return at;
            }
            proof {
                let closed = closed_by(text@, flag, before_frames, before_idx);
                lemma_machine_close(
                    text@,
                    flag,
                    before_rows,
                    rows@,
                    before_stack,
                    before_frames,
                    before_idx,
                    target,
                );
                frames = frames_after_close(before_frames, closed.0);
                idx = closed.1;
                assert(stack@ =~= before_stack.drop_last());
                assert(before_stack[0] == stack@[0]);
                lemma_machine_top(text@, flag, rows@, stack@, frames, idx, target);
            }
            let parent_pos = match stack.as_slice().get(stack.len().saturating_sub(1)) {
                Some(frame) => frame.pos,
                None => return at,
            };
            let (parent, _) = crate::tokenizer::exec::next_token(text, parent_pos as usize, flag);
            proof {
                assert(stack@.last() == stack@[stack.len() - 1]);
            }
            ending = ending_of(&parent);
        } else if opens(&token) {
            ending = ending_of(&token);
            let frame = ExecFrame { pos: at as u32, lo: rows.len() as u32 };
            stack.push(frame);
            proof {
                lemma_machine_open(
                    text@,
                    flag,
                    rows@,
                    before_stack,
                    before_frames,
                    before_idx,
                    target,
                    token_view,
                    frame,
                );
                frames = before_frames.push(ValueFrame { opening: token_view, value: Seq::empty() });
                idx = before_idx + 1;
                assert(stack@[0] == before_stack[0]);
            }
            at = after;
        } else {
            let start = rows.len() as u32;
            let row = ExecRow { pos: at as u32, start };
            rows.push(row);
            proof {
                lemma_extends_push(old_rows, before_rows, row);
                lemma_machine_leaf(
                    text@,
                    flag,
                    before_rows,
                    rows@,
                    before_stack,
                    before_frames,
                    before_idx,
                    target,
                    token_view,
                    at as u32,
                );
                frames = before_frames.update(
                    before_frames.len() - 1,
                    ValueFrame {
                        opening: before_frames.last().opening,
                        value: before_frames.last().value.push(
                            ComponentValue::Token { token: token_view },
                        ),
                    },
                );
                idx = before_idx + 1;
            }
            at = after;
        }
    }
}

} // verus!
