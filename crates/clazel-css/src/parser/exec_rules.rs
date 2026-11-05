//! At-rules, qualified rules and blocks, proven to meet [`super::contract`].
//!
//! "Consume a block's contents" and the rules it holds call each other, as deep as the page
//! likes. [`read_blocks`] is that recursion as a loop over an explicit stack, with
//! [`RuleFrame`]s as its ghost twin and [`rule_unwind`] for what the recursion does with
//! them, as in [`super::exec`].
//!
//! The text appends a block's waiting declarations once it knows a rule came back. Here
//! they go in before the rule's block is read, since a rule's items follow its block's in
//! the array. The two agree, because a rule that reaches its `{` always comes back: this
//! crate is a generic processor, so [`rule_is_valid`] holds.

#[allow(unused_imports)]
use super::contract::{at_index, position_of};
use super::exec::*;
use super::exec_declaration::*;
use super::exec_lists::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// The output, as it grows
// ------------------------------------------------------------------------------------

/// The three arrays of an [`ExecOutput`].
pub ghost struct Out {
    /// The rows.
    pub rows: Seq<ExecRow>,
    /// The declarations.
    pub decls: Seq<ExecDeclaration>,
    /// The items.
    pub items: Seq<ExecItem>,
}

/// True if item `k` refers only to what is there.
pub open spec fn item_wf(o: Out, k: int) -> bool {
    let item = o.items[k];
    &&& item.start <= k
    &&& item.kind is Declarations ==> item.hi <= o.decls.len()
    &&& !(item.kind is Declarations) ==> item.hi <= o.rows.len()
}

/// True if everything in `o` refers only to what is there.
pub open spec fn out_wf(o: Out) -> bool {
    &&& forall|j: int| 0 <= j < o.decls.len() ==> #[trigger] o.decls[j].value_hi <= o.rows.len()
    &&& forall|k: int| 0 <= k < o.items.len() ==> #[trigger] item_wf(o, k)
}

/// True if `n` is `o` with more on the end of some arrays.
pub open spec fn out_grows(o: Out, n: Out) -> bool {
    &&& extends(o.rows, n.rows)
    &&& o.decls.len() <= n.decls.len()
    &&& o.items.len() <= n.items.len()
    &&& forall|j: int| 0 <= j < o.decls.len() ==> o.decls[j] == n.decls[j]
    &&& forall|k: int| 0 <= k < o.items.len() ==> o.items[k] == n.items[k]
}

/// [`view_items`] of `o`.
pub open spec fn items_view(text: Seq<u32>, o: Out, lo: int, hi: int) -> Seq<BlockItem> {
    view_items(text, o.rows, o.decls, o.items, lo, hi)
}

/// [`view_item`] of `o`.
pub open spec fn item_view(text: Seq<u32>, o: Out, k: int) -> BlockItem {
    view_item(text, o.rows, o.decls, o.items, k)
}

/// [`view_declarations`] of `o`.
pub open spec fn decls_view(text: Seq<u32>, o: Out, lo: int, hi: int) -> Seq<Declaration> {
    view_declarations(text, o.rows, o.decls, lo, hi)
}

/// A declaration means the same while its rows stay.
pub proof fn lemma_agree_declaration(
    text: Seq<u32>,
    r1: Seq<ExecRow>,
    r2: Seq<ExecRow>,
    decl: ExecDeclaration,
)
    requires
        rows_agree(r1, r2, decl.value_hi as int),
    ensures
        view_declaration(text, r1, decl) == view_declaration(text, r2, decl),
{
    let lo = decl.value_lo as int;
    let hi = decl.value_hi as int;
    lemma_agree_list(text, false, r1, r2, lo, hi);
    lemma_agree_list(
        text.subrange(decl.text_start as int, decl.text_end as int),
        true,
        r1,
        r2,
        lo,
        hi,
    );
}

/// A list of declarations means the same as `o` grows.
pub proof fn lemma_agree_declarations(text: Seq<u32>, o: Out, n: Out, lo: int, hi: int)
    requires
        out_wf(o),
        out_grows(o, n),
        0 <= lo,
        hi <= o.decls.len(),
    ensures
        decls_view(text, o, lo, hi) == decls_view(text, n, lo, hi),
{
    let a = decls_view(text, o, lo, hi);
    let b = decls_view(text, n, lo, hi);
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        let d = o.decls[lo + i];
        assert(d == n.decls[lo + i]);
        assert(d.value_hi <= o.rows.len());
        assert forall|k: int| 0 <= k < d.value_hi implies o.rows[k] == n.rows[k] by {}
        lemma_agree_declaration(text, o.rows, n.rows, d);
    }
    assert(a =~= b);
}

/// An item means the same as `o` grows.
pub proof fn lemma_agree_item(text: Seq<u32>, o: Out, n: Out, k: int)
    requires
        out_wf(o),
        out_grows(o, n),
        0 <= k < o.items.len(),
    ensures
        item_view(text, o, k) == item_view(text, n, k),
    decreases k + 1, 0int,
{
    let item = o.items[k];
    assert(item == n.items[k]);
    assert(item_wf(o, k));
    if item.kind is Declarations {
        lemma_agree_declarations(text, o, n, item.lo as int, item.hi as int);
    } else {
        assert forall|j: int| 0 <= j < item.hi implies o.rows[j] == n.rows[j] by {}
        lemma_agree_list(text, false, o.rows, n.rows, item.lo as int, item.hi as int);
        lemma_agree_items(text, o, n, item.start as int, k);
    }
}

/// A list of items means the same as `o` grows.
pub proof fn lemma_agree_items(text: Seq<u32>, o: Out, n: Out, lo: int, hi: int)
    requires
        out_wf(o),
        out_grows(o, n),
        hi <= o.items.len(),
    ensures
        items_view(text, o, lo, hi) == items_view(text, n, lo, hi),
    decreases hi, 1int,
{
    if lo < 0 || hi <= lo {
    } else {
        assert(o.items[hi - 1] == n.items[hi - 1]);
        if o.items[hi - 1].start < hi {
            lemma_agree_items(text, o, n, lo, o.items[hi - 1].start as int);
            lemma_agree_item(text, o, n, hi - 1);
        }
    }
}

/// Well-formedness goes on, given that of what was added.
pub proof fn lemma_wf_grows(o: Out, n: Out)
    requires
        out_wf(o),
        out_grows(o, n),
        n.rows.len() >= o.rows.len(),
        forall|j: int| o.decls.len() <= j < n.decls.len() ==> #[trigger] n.decls[j].value_hi
            <= n.rows.len(),
        forall|k: int| o.items.len() <= k < n.items.len() ==> #[trigger] item_wf(n, k),
    ensures
        out_wf(n),
{
    assert forall|j: int| 0 <= j < n.decls.len() implies #[trigger] n.decls[j].value_hi
        <= n.rows.len() by {
        if j < o.decls.len() {
            assert(o.decls[j] == n.decls[j]);
            assert(o.decls[j].value_hi <= o.rows.len());
        }
    }
    assert forall|k: int| 0 <= k < n.items.len() implies #[trigger] item_wf(n, k) by {
        if k < o.items.len() {
            assert(o.items[k] == n.items[k]);
            assert(item_wf(o, k));
        }
    }
}

// ------------------------------------------------------------------------------------
// The custom property check of "consume a qualified rule"
// ------------------------------------------------------------------------------------

/// How far a prelude is through "an <ident-token> whose value starts with "--" followed by
/// a <colon-token>": 0 is nothing yet, 1 the ident, 2 both, and 3 is something else.
pub open spec fn custom_step(state: u8, value: ComponentValue) -> u8 {
    if is_whitespace_token(value) {
        state
    } else if state == 0 {
        if is_ident(value) && starts_with_two_dashes(token_value(value)) {
            1
        } else {
            3
        }
    } else if state == 1 {
        if is(value, Token::Colon) {
            2
        } else {
            3
        }
    } else {
        state
    }
}

/// [`custom_step`] through a whole list.
pub open spec fn custom_state(list: Seq<ComponentValue>) -> u8
    decreases list.len(),
{
    if list.len() == 0 {
        0
    } else {
        custom_step(custom_state(list.drop_last()), list.last())
    }
}

/// [`first_non_whitespace`] of a list with one more item.
proof fn lemma_fnw_push(list: Seq<ComponentValue>, value: ComponentValue, i: int)
    requires
        0 <= i <= list.len(),
    ensures
        first_non_whitespace(list, i) < list.len() ==> first_non_whitespace(list.push(value), i)
            == first_non_whitespace(list, i),
        first_non_whitespace(list, i) >= list.len() ==> first_non_whitespace(list.push(value), i)
            == if is_whitespace_token(value) {
            list.len() as int + 1
        } else {
            list.len() as int
        },
        i <= first_non_whitespace(list, i) <= list.len(),
    decreases list.len() - i,
{
    let bigger = list.push(value);
    if i < list.len() {
        assert(bigger[i] == list[i]);
        if is_whitespace_token(list[i]) {
            lemma_fnw_push(list, value, i + 1);
        }
    } else {
        assert(bigger[i] == value);
        assert(first_non_whitespace(bigger, i + 1) == bigger.len());
    }
}

/// What [`custom_state`] says of a list.
proof fn lemma_custom_state(list: Seq<ComponentValue>)
    ensures
        ({
            let n = list.len() as int;
            let first = first_non_whitespace(list, 0);
            let second = first_non_whitespace(list, first + 1);
            let word = first < n && is_ident(list[first]) && starts_with_two_dashes(
                token_value(list[first]),
            );
            let colon = second < n && is(list[second], Token::Colon);
            &&& (custom_state(list) == 0) == (first >= n)
            &&& (custom_state(list) == 1) == (word && second >= n)
            &&& (custom_state(list) == 2) == (word && colon)
            &&& custom_state(list) <= 3
        }),
    decreases list.len(),
{
    if list.len() > 0 {
        let shorter = list.drop_last();
        let value = list.last();
        assert(shorter.push(value) =~= list);
        lemma_custom_state(shorter);
        lemma_fnw_push(shorter, value, 0);
        let first = first_non_whitespace(shorter, 0);
        if first < shorter.len() {
            assert(list[first] == shorter[first]);
            lemma_fnw_push(shorter, value, first + 1);
            let second = first_non_whitespace(shorter, first + 1);
            if second < shorter.len() {
                assert(list[second] == shorter[second]);
            } else {
                assert(list[shorter.len() as int] == value);
            }
        } else {
            assert(list[shorter.len() as int] == value);
            assert(first_non_whitespace(list, shorter.len() as int + 1) == list.len());
        }
    } else {
        assert(first_non_whitespace(list, 0) == 0);
    }
}

/// [`prelude_looks_like_a_custom_property`], from the state.
pub proof fn lemma_custom_prelude(list: Seq<ComponentValue>)
    ensures
        prelude_looks_like_a_custom_property(list) == (custom_state(list) == 2),
{
    lemma_custom_state(list);
}

/// [`custom_step`] of a token.
fn custom_step_of(state: u8, token: &ExecToken) -> (r: u8)
    ensures
        r == custom_step(
            state,
            ComponentValue::Token { token: crate::tokenizer::exec::view_token(*token) },
        ),
{
    match token {
        ExecToken::Whitespace => state,
        ExecToken::Ident { value } => {
            if state == 0 {
                if value.len() >= 2 && value[0] == 0x2D && value[1] == 0x2D {
                    1
                } else {
                    3
                }
            } else if state == 1 {
                3
            } else {
                state
            }
        },
        ExecToken::Colon => {
            if state == 0 {
                3
            } else if state == 1 {
                2
            } else {
                state
            }
        },
        _ => {
            if state == 0 || state == 1 {
                3
            } else {
                state
            }
        },
    }
}

// ------------------------------------------------------------------------------------
// Preludes
// ------------------------------------------------------------------------------------

/// True if nothing has been lost of what `at_rule_loop` needs at `index`.
pub open spec fn at_prelude_stop(item: ComponentValue, nested: bool) -> bool {
    is(item, Token::Semicolon) || is(item, Token::Eof) || (nested && is(item, Token::CloseCurly))
        || is(item, Token::OpenCurly)
}

/// The values of an at-rule's prelude, up to what ends it.
fn read_at_prelude(
    text: &[u32],
    pos: usize,
    nested: bool,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
    Ghost(name): Ghost<Seq<u32>>,
) -> (r: (usize, Ghost<int>))
    requires
        text_requires(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        rows_fit(text@, false, old(rows).len() as nat, index),
    ensures
        ({
            let input = stream_of(text@, false);
            let lo = old(rows).len() as int;
            let prelude = view_list(text@, false, final(rows)@, lo, final(rows).len() as int);
            &&& at_index(text@, false, r.1@, r.0 as int)
            &&& extends(old(rows)@, final(rows)@)
            &&& lo <= final(rows).len()
            &&& paid(text@, false, lo as nat, index, final(rows).len() as nat, r.1@)
            &&& r.1@ >= index
            &&& pos <= r.0 <= text.len()
            &&& at_prelude_stop(next_token(input, r.1@), nested)
            &&& at_rule_loop(input, index, nested, name, Seq::empty()) == at_rule_loop(
                input,
                r.1@,
                nested,
                name,
                prelude,
            )
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost lo = rows.len() as int;
    let ghost old_rows = rows@;
    let ghost target = at_rule_loop(input, index, nested, name, Seq::empty());
    let mut at = pos;
    let ghost mut idx = index;
    proof {
        assert(view_list(text@, false, rows@, lo, lo) =~= Seq::<ComponentValue>::empty());
        assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {}
    }
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, false),
            at_index(text@, false, idx, at as int),
            pos <= at <= text.len(),
            index <= idx,
            lo == old_rows.len(),
            old_rows == old(rows)@,
            extends(old_rows, rows@),
            lo <= rows.len(),
            paid(text@, false, old_rows.len() as nat, index, rows.len() as nat, idx),
            rows_fit(text@, false, old_rows.len() as nat, index),
            at_rule_loop(
                input,
                idx,
                nested,
                name,
                view_list(text@, false, rows@, lo, rows.len() as int),
            ) == target,
            target == at_rule_loop(input, index, nested, name, Seq::empty()),
        decreases tokens_left(text@, false, idx),
    {
        let ghost before = rows@;
        let (token, next) = read_token(text, false, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Semicolon) || matches!(token, ExecToken::Eof)
            || matches!(token, ExecToken::OpenCurly) {
            return (at, Ghost(idx));
        } else if matches!(token, ExecToken::CloseCurly) {
            if nested {
                return (at, Ghost(idx));
            }
            let start = rows.len() as u32;
            rows.push(ExecRow { pos: at as u32, start });
            proof {
                lemma_token_added(text@, false, before, lo, at as u32, token_view);
                lemma_extends_chain(old_rows, before, rows@);
                idx = idx + 1;
            }
            at = next;
        } else {
            let end = read_component_value(text, false, token, at, next, rows, Ghost(idx));
            proof {
                let (value, after) = consume_a_component_value(input, idx);
                lemma_value_added(text@, false, before, rows@, lo, value);
                lemma_extends_chain(old_rows, before, rows@);
                idx = after;
            }
            at = end;
        }
    }
}

/// True if a qualified rule's prelude ends at `item`.
pub open spec fn qualified_prelude_stop(
    item: ComponentValue,
    stop_token: Option<Token>,
    nested: bool,
) -> bool {
    is(item, Token::Eof) || is_stop(item, stop_token) || (nested && is(item, Token::CloseCurly))
        || is(item, Token::OpenCurly)
}

/// The values of a qualified rule's prelude, up to what ends it. Also returns its
/// [`custom_state`].
fn read_qualified_prelude(
    text: &[u32],
    pos: usize,
    stop: u8,
    nested: bool,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
) -> (r: (usize, Ghost<int>, u8))
    requires
        text_requires(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        rows_fit(text@, false, old(rows).len() as nat, index),
    ensures
        ({
            let input = stream_of(text@, false);
            let lo = old(rows).len() as int;
            let prelude = view_list(text@, false, final(rows)@, lo, final(rows).len() as int);
            &&& at_index(text@, false, r.1@, r.0 as int)
            &&& extends(old(rows)@, final(rows)@)
            &&& lo <= final(rows).len()
            &&& paid(text@, false, lo as nat, index, final(rows).len() as nat, r.1@)
            &&& r.1@ >= index
            &&& pos <= r.0 <= text.len()
            &&& qualified_prelude_stop(next_token(input, r.1@), stop_token(stop), nested)
            &&& r.2 == custom_state(prelude)
            &&& qualified_rule_loop(
                input,
                index,
                stop_token(stop),
                nested,
                Seq::empty(),
            ) == qualified_rule_loop(input, r.1@, stop_token(stop), nested, prelude)
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost lo = rows.len() as int;
    let ghost old_rows = rows@;
    let ghost target = qualified_rule_loop(input, index, stop_token(stop), nested, Seq::empty());
    let mut at = pos;
    let ghost mut idx = index;
    let mut state: u8 = 0;
    proof {
        assert(view_list(text@, false, rows@, lo, lo) =~= Seq::<ComponentValue>::empty());
        assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {}
    }
    loop
        invariant
            text_requires(text@),
            input == stream_of(text@, false),
            at_index(text@, false, idx, at as int),
            pos <= at <= text.len(),
            index <= idx,
            lo == old_rows.len(),
            old_rows == old(rows)@,
            extends(old_rows, rows@),
            lo <= rows.len(),
            paid(text@, false, old_rows.len() as nat, index, rows.len() as nat, idx),
            rows_fit(text@, false, old_rows.len() as nat, index),
            state == custom_state(view_list(text@, false, rows@, lo, rows.len() as int)),
            qualified_rule_loop(
                input,
                idx,
                stop_token(stop),
                nested,
                view_list(text@, false, rows@, lo, rows.len() as int),
            ) == target,
            target == qualified_rule_loop(input, index, stop_token(stop), nested, Seq::empty()),
        decreases tokens_left(text@, false, idx),
    {
        let ghost before = rows@;
        let ghost values = view_list(text@, false, rows@, lo, rows.len() as int);
        let (token, next) = read_token(text, false, at, Ghost(idx));
        let ghost token_view = crate::tokenizer::exec::view_token(token);
        if matches!(token, ExecToken::Eof) || is_stop_token(&token, stop) || matches!(
            token,
            ExecToken::OpenCurly
        ) {
            return (at, Ghost(idx), state);
        } else if matches!(token, ExecToken::CloseCurly) {
            if nested {
                return (at, Ghost(idx), state);
            }
            state = custom_step_of(state, &token);
            let start = rows.len() as u32;
            rows.push(ExecRow { pos: at as u32, start });
            proof {
                lemma_token_added(text@, false, before, lo, at as u32, token_view);
                lemma_extends_chain(old_rows, before, rows@);
                let bigger = values.push(ComponentValue::Token { token: token_view });
                assert(bigger.drop_last() =~= values);
                idx = idx + 1;
            }
            at = next;
        } else {
            state = custom_step_of(state, &token);
            let leaf = !opens(&token);
            let end = read_component_value(text, false, token, at, next, rows, Ghost(idx));
            proof {
                let (value, after) = consume_a_component_value(input, idx);
                lemma_value_added(text@, false, before, rows@, lo, value);
                lemma_extends_chain(old_rows, before, rows@);
                let bigger = values.push(value);
                assert(bigger.drop_last() =~= values);
                assert(rows@[rows.len() - 1] == rows@.last());
                lemma_value_kind(text@, rows@, rows.len() - 1, token_view);
                idx = after;
            }
            at = end;
        }
    }
}

} // verus!
