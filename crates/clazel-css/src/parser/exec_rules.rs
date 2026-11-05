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
pub proof fn lemma_fnw_push(list: Seq<ComponentValue>, value: ComponentValue, i: int)
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
                if value.len() >= 2 && crate::tokenizer::exec::peek(value.as_slice(), 0) == 0x2D
                    && crate::tokenizer::exec::peek(value.as_slice(), 1) == 0x2D {
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

// ------------------------------------------------------------------------------------
// The frames
// ------------------------------------------------------------------------------------

/// What a block belongs to, which is what happens with its contents.
pub ghost enum Block {
    /// A block at-rule.
    AtRule {
        /// Its name.
        name: Seq<u32>,
        /// Its prelude.
        prelude: Seq<ComponentValue>,
    },
    /// A qualified rule.
    QualifiedRule {
        /// Its prelude.
        prelude: Seq<ComponentValue>,
    },
    /// "consume a block from input, and return nothing".
    Discard,
}

/// A block being read: the state of its "consume a block's contents".
pub ghost struct RuleFrame {
    /// What it belongs to.
    pub block: Block,
    /// "rules".
    pub rules: Seq<BlockItem>,
    /// "decls".
    pub decls: Seq<Declaration>,
}

/// The rule a block's contents make.
pub open spec fn outcome(block: Block, items: Seq<BlockItem>) -> Option<Rule> {
    match block {
        Block::AtRule { name, prelude } => Some(
            Rule::AtRule { name, prelude, child_rules: Some(items) },
        ),
        Block::QualifiedRule { prelude } => Some(qualified_rule_from(prelude, items)),
        Block::Discard => None,
    }
}

/// "Consume a block" at `index`, and the rule it makes.
pub open spec fn block_result(input: TokenStream, index: int, block: Block) -> (
    Option<Rule>,
    int,
) {
    let (items, next) = consume_a_block(input, index);
    (outcome(block, items), next)
}

/// A block's contents go on once one of their rules has come back.
pub open spec fn resume(
    input: TokenStream,
    frame: RuleFrame,
    out: Option<Rule>,
    next: int,
) -> (Seq<BlockItem>, int) {
    let flushed = with_declarations(frame.rules, frame.decls);
    match out {
        Some(rule) => blocks_contents_loop(
            input,
            next,
            flushed.push(BlockItem::Rule { rule }),
            Seq::empty(),
        ),
        None => blocks_contents_loop(input, next, flushed, Seq::empty()),
    }
}

/// What the spec's recursion does once the innermost block's contents gave `result`.
pub open spec fn rule_unwind(
    input: TokenStream,
    frames: Seq<RuleFrame>,
    result: (Seq<BlockItem>, int),
) -> (Option<Rule>, int)
    decreases frames.len(),
{
    if frames.len() == 0 {
        (None, result.1)
    } else {
        let out = outcome(frames.last().block, result.0);
        let next = discard_a_token(input, result.1);
        if frames.len() == 1 {
            (out, next)
        } else {
            rule_unwind(
                input,
                frames.drop_last(),
                resume(input, frames[frames.len() - 2], out, next),
            )
        }
    }
}

/// True if `item`, kept on the stack, is the rule of `block`.
pub open spec fn frame_ok(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    item: ExecItem,
    block: Block,
) -> bool {
    &&& item.hi <= rows.len()
    &&& match block {
        Block::AtRule { name, prelude } => {
            &&& item.kind is BlockAtRule
            &&& token_value(
                ComponentValue::Token { token: token_at(text, false, item.pos as int) },
            ) == name
            &&& view_list(text, false, rows, item.lo as int, item.hi as int) == prelude
        },
        Block::QualifiedRule { prelude } => {
            &&& item.kind is QualifiedRule
            &&& view_list(text, false, rows, item.lo as int, item.hi as int) == prelude
        },
        Block::Discard => item.kind is QualifiedRule,
    }
}

/// True if every frame but the top one's contents match the output.
#[verifier::opaque]
pub open spec fn frames_stable(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
) -> bool {
    &&& frames.len() == stack.len()
    &&& stack.len() > 0
    &&& forall|j: int|
        #![trigger stack[j]]
        0 <= j < stack.len() ==> stack[j].start <= o.items.len() && frame_ok(
            text,
            o.rows,
            stack[j],
            frames[j].block,
        )
    &&& forall|j: int|
        #![trigger stack[j]]
        1 <= j < stack.len() ==> stack[j - 1].start <= stack[j].start && frames[j - 1].rules
            == items_view(text, o, stack[j - 1].start as int, stack[j].start as int)
            && frames[j - 1].decls.len() == 0 && !(frames[j].block is Discard)
}

/// The invariant of [`read_blocks`]'s loop.
#[verifier::opaque]
pub open spec fn rule_machine(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
) -> bool {
        let top = frames.last();
    &&& out_wf(o)
    &&& frames_stable(text, o, stack, frames)
    &&& 0 <= cur <= o.decls.len()
    &&& top.rules == items_view(text, o, stack.last().start as int, o.items.len() as int)
    &&& top.decls == decls_view(text, o, cur, o.decls.len() as int)
    &&& rule_unwind(input, frames, blocks_contents_loop(input, index, top.rules, top.decls))
        == target
}

/// Frames stay right as the output grows.
proof fn lemma_stable_grows(
    text: Seq<u32>,
    o: Out,
    n: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
)
    requires
        out_wf(o),
        out_grows(o, n),
        frames_stable(text, o, stack, frames),
    ensures
        frames_stable(text, n, stack, frames),
{
    reveal(frames_stable);
    assert forall|j: int| #![trigger stack[j]] 0 <= j < stack.len() implies stack[j].start
        <= n.items.len() && frame_ok(text, n.rows, stack[j], frames[j].block) by {
        let item = stack[j];
        assert(frame_ok(text, o.rows, item, frames[j].block));
        assert forall|k: int| 0 <= k < item.hi implies o.rows[k] == n.rows[k] by {}
        lemma_agree_list(text, false, o.rows, n.rows, item.lo as int, item.hi as int);
    }
    assert forall|j: int| #![trigger stack[j]] 1 <= j < stack.len() implies stack[j - 1].start
        <= stack[j].start && frames[j - 1].rules == items_view(
        text,
        n,
        stack[j - 1].start as int,
        stack[j].start as int,
    ) && frames[j - 1].decls.len() == 0 && !(frames[j].block is Discard) by {
        lemma_agree_items(text, o, n, stack[j - 1].start as int, stack[j].start as int);
    }
}

/// What the steps read of [`frames_stable`].
proof fn lemma_stable_top(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
)
    requires
        frames_stable(text, o, stack, frames),
    ensures
        frames.len() == stack.len(),
        stack.len() > 0,
        stack.last().start <= o.items.len(),
        frame_ok(text, o.rows, stack.last(), frames.last().block),
        stack.len() >= 2 ==> stack[stack.len() - 2].start <= stack.last().start,
        stack.len() >= 2 ==> frames[frames.len() - 2].rules == items_view(
            text,
            o,
            stack[stack.len() - 2].start as int,
            stack.last().start as int,
        ),
        stack.len() >= 2 ==> frames[frames.len() - 2].decls.len() == 0,
        stack.len() >= 2 ==> !(frames.last().block is Discard),
{
    reveal(frames_stable);
    let m = stack.len() as int;
    assert(stack.last() == stack[m - 1]);
    assert(frames.last() == frames[m - 1]);
}

/// The top frame's contents do not matter to [`frames_stable`].
proof fn lemma_stable_update(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    rules: Seq<BlockItem>,
    decls: Seq<Declaration>,
)
    requires
        frames_stable(text, o, stack, frames),
    ensures
        frames_stable(
            text,
            o,
            stack,
            frames.update(
                frames.len() - 1,
                RuleFrame { block: frames.last().block, rules, decls },
            ),
        ),
{
    reveal(frames_stable);
    let m = frames.len() as int;
    let updated = frames.update(m - 1, RuleFrame { block: frames.last().block, rules, decls });
    assert(frames.last() == frames[m - 1]);
    assert forall|j: int| #![trigger stack[j]] 0 <= j < stack.len() implies stack[j].start
        <= o.items.len() && frame_ok(text, o.rows, stack[j], updated[j].block) by {}
    assert forall|j: int| #![trigger stack[j]] 1 <= j < stack.len() implies stack[j - 1].start
        <= stack[j].start && updated[j - 1].rules == items_view(
        text,
        o,
        stack[j - 1].start as int,
        stack[j].start as int,
    ) && updated[j - 1].decls.len() == 0 && !(updated[j].block is Discard) by {}
}

/// A new frame on top of one that has stopped.
proof fn lemma_stable_append(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    item: ExecItem,
    frame: RuleFrame,
)
    requires
        frames_stable(text, o, stack, frames),
        frames.last().rules == items_view(text, o, stack.last().start as int, o.items.len() as int),
        frames.last().decls.len() == 0,
        item.start == o.items.len(),
        frame_ok(text, o.rows, item, frame.block),
        !(frame.block is Discard),
    ensures
        frames_stable(text, o, stack.push(item), frames.push(frame)),
{
    reveal(frames_stable);
    let m = frames.len() as int;
    let pushed = frames.push(frame);
    let stack2 = stack.push(item);
    assert(frames.last() == frames[m - 1]);
    assert(stack.last() == stack[m - 1]);
    assert forall|j: int| #![trigger stack2[j]] 0 <= j < stack2.len() implies stack2[j].start
        <= o.items.len() && frame_ok(text, o.rows, stack2[j], pushed[j].block) by {
        if j < m {
            assert(stack2[j] == stack[j]);
            assert(pushed[j] == frames[j]);
        } else {
            assert(stack2[j] == item);
            assert(pushed[j] == frame);
        }
    }
    assert forall|j: int| #![trigger stack2[j]] 1 <= j < stack2.len() implies stack2[j - 1].start
        <= stack2[j].start && pushed[j - 1].rules == items_view(
        text,
        o,
        stack2[j - 1].start as int,
        stack2[j].start as int,
    ) && pushed[j - 1].decls.len() == 0 && !(pushed[j].block is Discard) by {
        assert(stack2[j - 1] == stack[j - 1]);
        assert(pushed[j - 1] == frames[j - 1]);
        if j < m {
            assert(stack2[j] == stack[j]);
            assert(pushed[j] == frames[j]);
        } else {
            assert(stack2[j] == item);
            assert(pushed[j] == frame);
        }
    }
}

/// A new frame on top of one that has stopped at `rules`.
proof fn lemma_stable_push(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    rules: Seq<BlockItem>,
    item: ExecItem,
    block: Block,
)
    requires
        frames_stable(text, o, stack, frames),
        rules == items_view(text, o, stack.last().start as int, o.items.len() as int),
        item.start == o.items.len(),
        frame_ok(text, o.rows, item, block),
        !(block is Discard),
    ensures
        frames_stable(
            text,
            o,
            stack.push(item),
            frames.update(
                frames.len() - 1,
                RuleFrame { block: frames.last().block, rules, decls: Seq::empty() },
            ).push(RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() }),
        ),
{
    lemma_stable_top(text, o, stack, frames);
    lemma_stable_update(text, o, stack, frames, rules, Seq::empty());
    let m = frames.len() as int;
    let updated = frames.update(
        m - 1,
        RuleFrame { block: frames.last().block, rules, decls: Seq::empty() },
    );
    assert(updated.last() == updated[m - 1]);
    lemma_stable_append(
        text,
        o,
        stack,
        updated,
        item,
        RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() },
    );
}

/// The top frame goes, and the one below it has `rules`.
proof fn lemma_stable_pop(
    text: Seq<u32>,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    rules: Seq<BlockItem>,
)
    requires
        frames_stable(text, o, stack, frames),
        stack.len() >= 2,
    ensures
        frames_stable(
            text,
            o,
            stack.drop_last(),
            frames.drop_last().update(
                frames.len() - 2,
                RuleFrame {
                    block: frames[frames.len() - 2].block,
                    rules,
                    decls: Seq::empty(),
                },
            ),
        ),
{
    reveal(frames_stable);
    let m = frames.len() as int;
    let s2 = stack.drop_last();
    let updated = frames.drop_last().update(
        m - 2,
        RuleFrame { block: frames[m - 2].block, rules, decls: Seq::empty() },
    );
    assert forall|j: int| #![trigger s2[j]] 0 <= j < s2.len() implies s2[j].start <= o.items.len()
        && frame_ok(text, o.rows, s2[j], updated[j].block) by {
        assert(s2[j] == stack[j]);
        assert(updated[j].block == frames[j].block);
    }
    assert forall|j: int| #![trigger s2[j]] 1 <= j < s2.len() implies s2[j - 1].start <= s2[j].start
        && updated[j - 1].rules == items_view(
        text,
        o,
        s2[j - 1].start as int,
        s2[j].start as int,
    ) && updated[j - 1].decls.len() == 0 && !(updated[j].block is Discard) by {
        assert(s2[j] == stack[j]);
        assert(s2[j - 1] == stack[j - 1]);
        assert(updated[j - 1] == frames[j - 1]);
        assert(updated[j].block == frames[j].block);
    }
    assert(updated.len() == s2.len());
    assert(updated.last() == updated[m - 2]);
}

/// [`rule_unwind`] does not look at the top frame's contents.
proof fn lemma_unwind_top(
    input: TokenStream,
    frames: Seq<RuleFrame>,
    rules: Seq<BlockItem>,
    decls: Seq<Declaration>,
    result: (Seq<BlockItem>, int),
)
    requires
        frames.len() > 0,
    ensures
        rule_unwind(
            input,
            frames.update(
                frames.len() - 1,
                RuleFrame { block: frames.last().block, rules, decls },
            ),
            result,
        ) == rule_unwind(input, frames, result),
{
    let n = frames.len() as int;
    let updated = frames.update(n - 1, RuleFrame { block: frames.last().block, rules, decls });
    assert(updated.drop_last() =~= frames.drop_last());
    assert(updated.last().block == frames.last().block);
    if n >= 2 {
        assert(updated[n - 2] == frames[n - 2]);
    }
}

/// The first step: the block at `index`, of `block`.
proof fn lemma_rule_start(
    text: Seq<u32>,
    input: TokenStream,
    o: Out, first: ExecItem, block: Block, index: int)
    requires
        out_wf(o),
        first.start == o.items.len(),
        frame_ok(text, o.rows, first, block),
        is(next_token(input, index), Token::OpenCurly),
    ensures
        rule_machine(
            text,
            input,
            o,
            seq![first],
            seq![RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() }],
            o.decls.len() as int,
            index + 1,
            block_result(input, index, block),
        ),
{
    reveal(rule_machine);
    reveal(frames_stable);
    let stack = seq![first];
    let frames = seq![RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() }];
    let hi = o.items.len() as int;
    assert(stack.last() == first);
    assert(frames.last() == frames[0]);
    assert(stack[0] == first);
    assert(items_view(text, o, hi, hi) =~= Seq::<BlockItem>::empty());
    assert(decls_view(text, o, o.decls.len() as int, o.decls.len() as int)
        =~= Seq::<Declaration>::empty());
    assert(discard_a_token(input, index) == index + 1);
}

/// `<whitespace-token>`, `<semicolon-token>`: "Discard a token from input."
proof fn lemma_rule_skip(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is(next_token(input, index), Token::Whitespace) || is(
            next_token(input, index),
            Token::Semicolon,
        ),
    ensures
        rule_machine(text, input, o, stack, frames, cur, index + 1, target),
{
    reveal(rule_machine);
}

/// Rows were added, and nothing else.
proof fn lemma_rule_rows(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    n: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        extends(o.rows, n.rows),
        o.rows.len() <= n.rows.len(),
        n.decls == o.decls,
        n.items == o.items,
    ensures
        rule_machine(text, input, n, stack, frames, cur, index, target),
        out_grows(o, n),
{
    reveal(rule_machine);
    assert(out_grows(o, n));
    lemma_wf_grows(o, n);
    lemma_stable_top(text, o, stack, frames);
    lemma_stable_grows(text, o, n, stack, frames);
    lemma_agree_items(
        text,
        o,
        n,
        stack.last().start as int,
        o.items.len() as int,
    );
    lemma_agree_declarations(text, o, n, cur, o.decls.len() as int);
}

/// True if the next token is what "anything else" stands for in a block's contents.
pub open spec fn is_anything_else(item: ComponentValue) -> bool {
    !(is(item, Token::Whitespace) || is(item, Token::Semicolon) || is(item, Token::Eof) || is(
        item,
        Token::CloseCurly,
    ) || is_at_keyword(item))
}

/// A declaration came back.
proof fn lemma_rule_declaration(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    n: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
    decl: Declaration,
    next: int,
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is_anything_else(next_token(input, index)),
        consume_a_declaration(input, index, true) == (Some(decl), next),
        next > index,
        extends(o.rows, n.rows),
        o.rows.len() <= n.rows.len(),
        n.items == o.items,
        n.decls.len() == o.decls.len() + 1,
        n.decls.drop_last() == o.decls,
        n.decls.last().value_hi == n.rows.len(),
        view_declaration(text, n.rows, n.decls.last()) == decl,
    ensures
        rule_machine(
            text,
            input,
            n,
            stack,
            frames.update(
                frames.len() - 1,
                RuleFrame {
                    block: frames.last().block,
                    rules: frames.last().rules,
                    decls: frames.last().decls.push(decl),
                },
            ),
            cur,
            next,
            target,
        ),
        out_grows(o, n),
{
    reveal(rule_machine);
    let top = frames.last();
    let m = frames.len() as int;
    let updated = frames.update(
        m - 1,
        RuleFrame { block: top.block, rules: top.rules, decls: top.decls.push(decl) },
    );
    assert forall|j: int| 0 <= j < o.decls.len() implies o.decls[j] == n.decls[j] by {
        assert(n.decls.drop_last()[j] == n.decls[j]);
    }
    assert(out_grows(o, n));
    assert(n.decls[n.decls.len() - 1] == n.decls.last());
    lemma_wf_grows(o, n);
    lemma_stable_top(text, o, stack, frames);
    lemma_stable_grows(text, o, n, stack, frames);
    lemma_stable_update(text, n, stack, frames, top.rules, top.decls.push(decl));
    lemma_agree_items(text, o, n, stack.last().start as int, o.items.len() as int);
    lemma_agree_declarations(text, o, n, cur, o.decls.len() as int);
    let before = decls_view(text, n, cur, o.decls.len() as int);
    let after = decls_view(text, n, cur, n.decls.len() as int);
    assert(after =~= before.push(decl));
    lemma_unwind_top(
        input,
        frames,
        top.rules,
        top.decls.push(decl),
        blocks_contents_loop(input, next, top.rules, top.decls.push(decl)),
    );
}

/// No declaration, and no rule either.
proof fn lemma_rule_nothing(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
    next: int,
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is_anything_else(next_token(input, index)),
        consume_a_declaration(input, index, true).0 is None,
        consume_a_qualified_rule(input, index, Some(Token::Semicolon), true) == (
            QualifiedRuleResult::Nothing,
            next,
        ),
    ensures
        rule_machine(text, input, o, stack, frames, cur, next, target),
        next > index,
{
    reveal(rule_machine);
    super::termination::lemma_qualified_rule_forward(
        input,
        index,
        Some(Token::Semicolon),
        true,
        Seq::empty(),
    );
}

/// The declarations waiting in a block go in as one item.
fn flush_declarations(items: &mut Vec<ExecItem>, decls_len: usize, cur: usize)
    requires
        old(items).len() < u32::MAX,
        decls_len < u32::MAX,
        cur <= decls_len,
    ensures
        cur == decls_len ==> final(items)@ == old(items)@,
        cur < decls_len ==> final(items)@ == old(items)@.push(
            ExecItem {
                kind: ExecItemKind::Declarations,
                pos: 0,
                start: old(items).len() as u32,
                lo: cur as u32,
                hi: decls_len as u32,
            },
        ),
{
    if cur < decls_len {
        let start = items.len() as u32;
        items.push(
            ExecItem {
                kind: ExecItemKind::Declarations,
                pos: 0,
                start,
                lo: cur as u32,
                hi: decls_len as u32,
            },
        );
    }
}

/// What the flush of `cur` gives.
pub open spec fn flushed_items(o: Out, cur: int) -> Seq<ExecItem> {
    if cur < o.decls.len() {
        o.items.push(
            ExecItem {
                kind: ExecItemKind::Declarations,
                pos: 0,
                start: o.items.len() as u32,
                lo: cur as u32,
                hi: o.decls.len() as u32,
            },
        )
    } else {
        o.items
    }
}

/// Flushing does what the text does with "decls".
proof fn lemma_flushed(text: Seq<u32>, o: Out, f: Out, start: int, cur: int)
    requires
        out_wf(o),
        0 <= start <= o.items.len(),
        0 <= cur <= o.decls.len(),
        o.decls.len() < u32::MAX,
        o.items.len() < u32::MAX,
        f == (Out { rows: o.rows, decls: o.decls, items: flushed_items(o, cur) }),
    ensures
        out_wf(f),
        out_grows(o, f),
        items_view(text, f, start, f.items.len() as int) == with_declarations(
            items_view(text, o, start, o.items.len() as int),
            decls_view(text, o, cur, o.decls.len() as int),
        ),
{
    let k = o.items.len() as int;
    assert forall|j: int| 0 <= j < o.rows.len() implies o.rows[j] == f.rows[j] by {}
    assert(out_grows(o, f));
    if cur < o.decls.len() {
        assert(f.items[k] == f.items.last());
        assert(item_wf(f, k));
        lemma_wf_grows(o, f);
        lemma_agree_items(text, o, f, start, k);
        assert(item_view(text, f, k) == (BlockItem::Declarations {
            declarations: decls_view(text, o, cur, o.decls.len() as int),
        }));
        assert(decls_view(text, o, cur, o.decls.len() as int).len() > 0);
    } else {
        assert(decls_view(text, o, cur, o.decls.len() as int) =~= Seq::<Declaration>::empty());
        assert(f == o);
    }
}

/// An at-rule with no block goes on the end of the block's items.
proof fn lemma_rule_statement(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    f: Out,
    n: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
    rule: Rule,
    next: int,
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is_at_keyword(next_token(input, index)),
        consume_an_at_rule(input, index, true) == (Some(rule), next),
        o.decls.len() < u32::MAX,
        o.items.len() + 1 < u32::MAX,
        f == (Out { rows: o.rows, decls: o.decls, items: flushed_items(o, cur) }),
        n.rows == f.rows,
        n.decls == f.decls,
        n.items.len() == f.items.len() + 1,
        n.items.drop_last() == f.items,
        n.items.last().start == f.items.len(),
        n.items.last().hi <= n.rows.len(),
        !(n.items.last().kind is Declarations),
        item_view(text, n, f.items.len() as int) == (BlockItem::Rule { rule }),
    ensures
        rule_machine(
            text,
            input,
            n,
            stack,
            frames.update(
                frames.len() - 1,
                RuleFrame {
                    block: frames.last().block,
                    rules: with_declarations(frames.last().rules, frames.last().decls).push(
                        BlockItem::Rule { rule },
                    ),
                    decls: Seq::empty(),
                },
            ),
            n.decls.len() as int,
            next,
            target,
        ),
{
    reveal(rule_machine);
    let top = frames.last();
    let m = frames.len() as int;
    let rules = with_declarations(top.rules, top.decls).push(BlockItem::Rule { rule });
    let updated = frames.update(
        m - 1,
        RuleFrame { block: top.block, rules, decls: Seq::empty() },
    );
    let k = f.items.len() as int;
    lemma_stable_top(text, o, stack, frames);
    lemma_flushed(text, o, f, stack.last().start as int, cur);
    assert forall|j: int| 0 <= j < f.items.len() implies f.items[j] == n.items[j] by {
        assert(n.items.drop_last()[j] == n.items[j]);
    }
    assert forall|j: int| 0 <= j < f.rows.len() implies f.rows[j] == n.rows[j] by {}
    assert(out_grows(f, n));
    assert(n.items[k] == n.items.last());
    assert(item_wf(n, k));
    lemma_wf_grows(f, n);
    lemma_stable_grows(text, o, f, stack, frames);
    lemma_stable_grows(text, f, n, stack, frames);
    lemma_stable_update(text, n, stack, frames, rules, Seq::empty());
    lemma_agree_items(text, f, n, stack.last().start as int, k);
    assert(decls_view(text, n, n.decls.len() as int, n.decls.len() as int)
        =~= Seq::<Declaration>::empty());
    super::termination::lemma_at_rule_advances(input, index, true);
    lemma_unwind_top(
        input,
        frames,
        rules,
        Seq::empty(),
        blocks_contents_loop(input, next, rules, Seq::empty()),
    );
}

/// A rule's block opens: a new frame, and the block around it stops at its waiting
/// declarations. `resume` of what the block makes must be what the spec does from here.
proof fn lemma_rule_push(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    f: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
    item: ExecItem,
    block: Block,
    open: int,
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        o.decls.len() < u32::MAX,
        o.items.len() < u32::MAX,
        f == (Out { rows: o.rows, decls: o.decls, items: flushed_items(o, cur) }),
        item.start == f.items.len(),
        frame_ok(text, f.rows, item, block),
        !(block is Discard),
        is(next_token(input, open), Token::OpenCurly),
        ({
                        let result = block_result(input, open, block);
            resume(input, frames.last(), result.0, result.1) == blocks_contents_loop(
                input,
                index,
                frames.last().rules,
                frames.last().decls,
            )
        }),
    ensures
        rule_machine(
            text,
            input,
            f,
            stack.push(item),
            frames.update(
                frames.len() - 1,
                RuleFrame {
                    block: frames.last().block,
                    rules: with_declarations(frames.last().rules, frames.last().decls),
                    decls: Seq::empty(),
                },
            ).push(RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() }),
            f.decls.len() as int,
            open + 1,
            target,
        ),
{
    reveal(rule_machine);
    let top = frames.last();
    let m = frames.len() as int;
    let flushed = with_declarations(top.rules, top.decls);
    let parent = RuleFrame { block: top.block, rules: flushed, decls: Seq::empty() };
    let updated = frames.update(m - 1, parent);
    let new_frame = RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() };
    let pushed = updated.push(new_frame);
    let stack2 = stack.push(item);
    lemma_stable_top(text, o, stack, frames);
    lemma_flushed(text, o, f, stack.last().start as int, cur);
    lemma_stable_grows(text, o, f, stack, frames);
    lemma_agree_items(text, o, f, stack.last().start as int, o.items.len() as int);
    lemma_agree_declarations(text, o, f, cur, o.decls.len() as int);
    lemma_stable_push(text, f, stack, frames, flushed, item, block);
    assert(stack2.last() == item);
    assert(pushed.last() == new_frame);
    let hi = f.items.len() as int;
    assert(items_view(text, f, hi, hi) =~= Seq::<BlockItem>::empty());
    assert(decls_view(text, f, f.decls.len() as int, f.decls.len() as int)
        =~= Seq::<Declaration>::empty());
    // Unwinding the new frame gives what the block makes, and then the old top resumes.
    let contents = blocks_contents_loop(input, open + 1, Seq::empty(), Seq::empty());
    let result = block_result(input, open, block);
    assert(discard_a_token(input, open) == open + 1);
    assert(result == (outcome(block, contents.0), discard_a_token(input, contents.1)));
    assert(pushed.drop_last() =~= updated);
    assert(pushed[m - 1] == parent);
    assert(with_declarations(flushed, Seq::empty()) == flushed);
    assert(resume(input, parent, result.0, result.1) == resume(input, top, result.0, result.1));
    lemma_unwind_top(
        input,
        frames,
        flushed,
        Seq::empty(),
        blocks_contents_loop(input, index, top.rules, top.decls),
    );
}

/// The item of a block's rule means what the block makes.
proof fn lemma_frame_item(
    text: Seq<u32>,
    n: Out,
    k: int,
    block: Block,
    items: Seq<BlockItem>,
)
    requires
        0 <= k < n.items.len(),
        frame_ok(text, n.rows, n.items[k], block),
        !(block is Discard),
        items_view(text, n, n.items[k].start as int, k) == items,
    ensures
        item_view(text, n, k) == (BlockItem::Rule { rule: outcome(block, items).unwrap() }),
{
}

/// A block ends and there is one around it.
proof fn lemma_rule_close(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    f: Out,
    n: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is(next_token(input, index), Token::Eof) || is(
            next_token(input, index),
            Token::CloseCurly,
        ),
        stack.len() >= 2,
        o.decls.len() < u32::MAX,
        o.items.len() + 1 < u32::MAX,
        f == (Out { rows: o.rows, decls: o.decls, items: flushed_items(o, cur) }),
        n == (Out { rows: f.rows, decls: f.decls, items: f.items.push(stack.last()) }),
    ensures
        ({
                        let m = frames.len() as int;
            let parent = frames[m - 2];
            let rule = closed_rule(text, o, frames, stack, cur);
            rule_machine(
                text,
                input,
                n,
                stack.drop_last(),
                frames.drop_last().update(
                    m - 2,
                    RuleFrame {
                        block: parent.block,
                        rules: parent.rules.push(BlockItem::Rule { rule }),
                        decls: Seq::empty(),
                    },
                ),
                n.decls.len() as int,
                discard_a_token(input, index),
                target,
            )
        }),
{
    reveal(rule_machine);
    let m = frames.len() as int;
    let top = frames.last();
    let parent = frames[m - 2];
    let frame = stack.last();
    let k = f.items.len() as int;
    let items_list = with_declarations(top.rules, top.decls);
    let rule = closed_rule(text, o, frames, stack, cur);
    assert(frames[m - 1] == top);
    lemma_stable_top(text, o, stack, frames);
    lemma_flushed(text, o, f, frame.start as int, cur);
    lemma_stable_grows(text, o, f, stack, frames);
    assert forall|j: int| 0 <= j < f.items.len() implies f.items[j] == n.items[j] by {}
    assert forall|j: int| 0 <= j < f.rows.len() implies f.rows[j] == n.rows[j] by {}
    assert(out_grows(f, n));
    assert(n.items[k] == frame);
    assert(frame.start <= k);
    assert(item_wf(n, k)) by {
        assert(!(frame.kind is Declarations)) by {
            match top.block {
                Block::AtRule { .. } => {},
                Block::QualifiedRule { .. } => {},
                Block::Discard => {},
            }
        }
    }
    lemma_wf_grows(f, n);
    lemma_stable_grows(text, f, n, stack, frames);
    lemma_agree_items(text, f, n, frame.start as int, k);
    lemma_stable_top(text, n, stack, frames);
    lemma_frame_item(text, n, k, top.block, items_list);
    assert(outcome(top.block, items_list) == Some(rule));
    // The parent's list now ends in this rule.
    let s2 = stack.drop_last();
    let updated = frames.drop_last().update(
        m - 2,
        RuleFrame {
            block: parent.block,
            rules: parent.rules.push(BlockItem::Rule { rule }),
            decls: Seq::empty(),
        },
    );
    assert(stack[m - 2] == s2.last());
    assert(updated.last() == updated[m - 2]);
    assert(frame.start <= k);
    assert(frame.start < k + 1);
    assert(items_view(text, n, stack[m - 2].start as int, k + 1) == items_view(
        text,
        n,
        stack[m - 2].start as int,
        frame.start as int,
    ).push(item_view(text, n, k)));
    assert(decls_view(text, n, n.decls.len() as int, n.decls.len() as int)
        =~= Seq::<Declaration>::empty());
    lemma_stable_pop(text, n, stack, frames, parent.rules.push(BlockItem::Rule { rule }));
    assert(with_declarations(parent.rules, parent.decls) == parent.rules);
    let next = discard_a_token(input, index);
    let rules = parent.rules.push(BlockItem::Rule { rule });
    assert(blocks_contents_loop(input, index, top.rules, top.decls) == (items_list, index));
    assert(resume(input, parent, Some(rule), next) == blocks_contents_loop(
        input,
        next,
        rules,
        Seq::empty(),
    ));
    lemma_unwind_top(
        input,
        frames.drop_last(),
        rules,
        Seq::empty(),
        blocks_contents_loop(input, next, rules, Seq::empty()),
    );
    assert(frames.drop_last().last() == parent);
}

/// The rule the top frame makes.
pub open spec fn closed_rule(
    text: Seq<u32>,
    o: Out,
    frames: Seq<RuleFrame>,
    stack: Seq<ExecItem>,
    cur: int,
) -> Rule {
    outcome(
        frames.last().block,
        with_declarations(frames.last().rules, frames.last().decls),
    ).unwrap()
}

/// The first block ends, which ends the call.
proof fn lemma_rule_done(
    text: Seq<u32>,
    input: TokenStream,
    o: Out,
    f: Out,
    stack: Seq<ExecItem>,
    frames: Seq<RuleFrame>,
    cur: int,
    index: int,
    target: (Option<Rule>, int),
)
    requires
        rule_machine(text, input, o, stack, frames, cur, index, target),
        is(next_token(input, index), Token::Eof) || is(
            next_token(input, index),
            Token::CloseCurly,
        ),
        stack.len() == 1,
        o.decls.len() < u32::MAX,
        o.items.len() < u32::MAX,
        f == (Out { rows: o.rows, decls: o.decls, items: flushed_items(o, cur) }),
    ensures
        out_wf(f),
        out_grows(o, f),
        target == (
            outcome(
                frames.last().block,
                items_view(text, f, stack.last().start as int, f.items.len() as int),
            ),
            discard_a_token(input, index),
        ),
        frame_ok(text, o.rows, stack.last(), frames.last().block),
        stack.last().start <= o.items.len(),
{
    reveal(rule_machine);
    let top = frames.last();
    lemma_stable_top(text, o, stack, frames);
    lemma_flushed(text, o, f, stack.last().start as int, cur);
    assert(blocks_contents_loop(input, index, top.rules, top.decls) == (
        with_declarations(top.rules, top.decls),
        index,
    ));
}

// ------------------------------------------------------------------------------------
// The heads of rules
// ------------------------------------------------------------------------------------

/// What the text being parsed must be: small enough that every place fits a `u32`.
pub open spec fn text_fits(text: Seq<u32>) -> bool {
    &&& text_requires(text)
    &&& text.len() <= 0x2000_0000
    &&& stream_of(text, false).tokens.len() <= text.len() + 1
}

/// The name of the at-rule at `index`.
pub open spec fn at_name(input: TokenStream, index: int) -> Seq<u32> {
    token_value(next_token(input, index))
}

/// An at-rule, up to the end of a statement or past the `{` of its block.
pub fn read_at_head(
    text: &[u32],
    pos: usize,
    nested: bool,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
) -> (r: (bool, usize, Ghost<int>, ExecItem))
    requires
        text_fits(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        is_at_keyword(next_token(stream_of(text@, false), index)),
        room(text@, old(rows).len() as nat, index, pos as int),
    ensures
        ({
            let input = stream_of(text@, false);
            let lo = old(rows).len() as int;
            let hi = final(rows).len() as int;
            let name = at_name(input, index);
            let prelude = view_list(text@, false, final(rows)@, lo, hi);
            &&& extends(old(rows)@, final(rows)@)
            &&& lo <= hi
            &&& r.2@ > index
            &&& pos <= r.1 <= text.len()
            &&& r.3.pos == pos
            &&& r.3.lo == lo
            &&& r.3.hi == hi
            &&& token_value(
                ComponentValue::Token { token: token_at(text@, false, pos as int) },
            ) == name
            &&& r.0 ==> r.3.kind is StatementAtRule
            &&& r.0 ==> consume_an_at_rule(input, index, nested) == (
                Some(Rule::AtRule { name, prelude, child_rules: None }),
                r.2@,
            )
            &&& r.0 ==> at_index(text@, false, r.2@, r.1 as int)
            &&& r.0 ==> room(text@, hi as nat, r.2@, r.1 as int)
            &&& !r.0 ==> r.3.kind is BlockAtRule
            &&& !r.0 ==> is(next_token(input, r.2@), Token::OpenCurly)
            &&& !r.0 ==> consume_an_at_rule(input, index, nested) == block_result(
                input,
                r.2@,
                Block::AtRule { name, prelude },
            )
            &&& !r.0 ==> at_index(text@, false, r.2@ + 1, r.1 as int)
            &&& !r.0 ==> room(text@, hi as nat, r.2@ + 1, r.1 as int)
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost name = at_name(input, index);
    let lo = rows.len();
    let (_, next) = read_token(text, false, pos, Ghost(index));
    let (at, Ghost(j)) = read_at_prelude(text, next, nested, rows, Ghost(index + 1), Ghost(name));
    let hi = rows.len();
    let (token, after) = read_token(text, false, at, Ghost(j));
    if matches!(token, ExecToken::OpenCurly) {
        return (
            false,
            after,
            Ghost(j),
            ExecItem {
                kind: ExecItemKind::BlockAtRule,
                pos: pos as u32,
                start: 0,
                lo: lo as u32,
                hi: hi as u32,
            },
        );
    }
    let item = ExecItem {
        kind: ExecItemKind::StatementAtRule,
        pos: pos as u32,
        start: 0,
        lo: lo as u32,
        hi: hi as u32,
    };
    if matches!(token, ExecToken::Semicolon) {
        (true, after, Ghost(j + 1), item)
    } else {
        (true, at, Ghost(j), item)
    }
}

/// What a qualified rule's result is as a rule.
pub open spec fn as_option(result: QualifiedRuleResult) -> Option<Rule> {
    match result {
        QualifiedRuleResult::Rule { rule } => Some(rule),
        _ => None,
    }
}

/// A qualified rule, up to where it gives nothing, or past the `{` of its block. The first
/// result is 0 for nothing, 1 for a block that makes a rule, and 2 for a block to discard.
pub fn read_qualified_head(
    text: &[u32],
    pos: usize,
    stop: u8,
    nested: bool,
    rows: &mut Vec<ExecRow>,
    Ghost(index): Ghost<int>,
) -> (r: (u8, usize, Ghost<int>))
    requires
        text_fits(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        room(text@, old(rows).len() as nat, index, pos as int),
    ensures
        ({
            let input = stream_of(text@, false);
            let lo = old(rows).len() as int;
            let hi = final(rows).len() as int;
            let prelude = view_list(text@, false, final(rows)@, lo, hi);
            let (result, after) = consume_a_qualified_rule(input, index, stop_token(stop), nested);
            &&& extends(old(rows)@, final(rows)@)
            &&& lo <= hi
            &&& r.2@ >= index
            &&& pos <= r.1 <= text.len()
            &&& r.0 <= 2
            &&& r.0 == 0 ==> result is Nothing
            &&& r.0 == 0 ==> r.2@ == after
            &&& r.0 == 0 ==> final(rows)@ == old(rows)@
            &&& r.0 == 0 ==> at_index(text@, false, r.2@, r.1 as int)
            &&& r.0 == 0 ==> room(text@, hi as nat, r.2@, r.1 as int)
            &&& r.0 != 0 ==> is(next_token(input, r.2@), Token::OpenCurly)
            &&& r.0 != 0 ==> at_index(text@, false, r.2@ + 1, r.1 as int)
            &&& r.0 != 0 ==> room(text@, hi as nat, r.2@ + 1, r.1 as int)
            &&& r.0 == 1 ==> (as_option(result), after) == block_result(
                input,
                r.2@,
                Block::QualifiedRule { prelude },
            )
            &&& r.0 == 1 ==> result is Rule
            &&& r.0 == 2 ==> (as_option(result), after) == block_result(
                input,
                r.2@,
                Block::Discard,
            )
            &&& r.0 == 2 ==> !nested
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost old_rows = rows@;
    let lo = rows.len();
    let (at, Ghost(j), state) = read_qualified_prelude(text, pos, stop, nested, rows, Ghost(index));
    let ghost prelude = view_list(text@, false, rows@, lo as int, rows.len() as int);
    proof {
        lemma_custom_prelude(prelude);
    }
    let (token, after) = read_token(text, false, at, Ghost(j));
    if !matches!(token, ExecToken::OpenCurly) {
        let ghost whole = rows@;
        rows.truncate(lo);
        proof {
            assert(rows@ =~= old_rows) by {
                assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {
                    assert(old_rows[k] == whole[k]);
                }
            }
        }
        return (0, at, Ghost(j));
    }
    if state == 2 {
        if nested {
            let ghost whole = rows@;
            rows.truncate(lo);
            proof {
                assert(rows@ =~= old_rows) by {
                    assert forall|k: int| 0 <= k < old_rows.len() implies old_rows[k] == rows@[k] by {
                        assert(old_rows[k] == whole[k]);
                    }
                }
            }
            let (end, Ghost(k)) = read_remnants(text, false, at, true, Ghost(j));
            return (0, end, Ghost(k));
        }
        return (2, after, Ghost(j));
    }
    (1, after, Ghost(j))
}

// ------------------------------------------------------------------------------------
// Blocks
// ------------------------------------------------------------------------------------

/// A rule that came back: "If decls is not empty, append it to rules", then the rule. This
/// is the at-keyword branch of "consume a block's contents".
proof fn lemma_contents_at(
    input: TokenStream,
    top: RuleFrame,
    index: int,
    rule: Rule,
    next: int,
)
    requires
        is_at_keyword(next_token(input, index)),
        consume_an_at_rule(input, index, true) == (Some(rule), next),
    ensures
        resume(input, top, Some(rule), next) == blocks_contents_loop(
            input,
            index,
            top.rules,
            top.decls,
        ),
{
    super::termination::lemma_at_rule_advances(input, index, true);
}

/// Likewise, for the "anything else" branch.
proof fn lemma_contents_qualified(
    input: TokenStream,
    top: RuleFrame,
    index: int,
    rule: Rule,
    next: int,
)
    requires
        is_anything_else(next_token(input, index)),
        consume_a_declaration(input, index, true).0 is None,
        consume_a_qualified_rule(input, index, Some(Token::Semicolon), true) == (
            QualifiedRuleResult::Rule { rule },
            next,
        ),
    ensures
        resume(input, top, Some(rule), next) == blocks_contents_loop(
            input,
            index,
            top.rules,
            top.decls,
        ),
{
    super::termination::lemma_qualified_rule_forward(
        input,
        index,
        Some(Token::Semicolon),
        true,
        Seq::empty(),
    );
}

/// The arrays as they stand.
pub open spec fn out_of(
    rows: Seq<ExecRow>,
    decls: Seq<ExecDeclaration>,
    items: Seq<ExecItem>,
) -> Out {
    Out { rows, decls, items }
}

/// How much of the arrays' `u32` space a step has used. A token pays for 3 items: a block's
/// `{` pays for the declarations waiting before it and for the rule and the declarations
/// inside it, which each open block holds 2 for.
pub open spec fn budget(decls: nat, items: nat, stack: nat, index: int) -> bool {
    decls <= index && items + 2 * stack <= 3 * index
}

/// [`out_grows`] goes through.
pub proof fn lemma_grows_chain(a: Out, b: Out, c: Out)
    requires
        out_grows(a, b),
        out_grows(b, c),
    ensures
        out_grows(a, c),
{
    lemma_extends_chain(a.rows, b.rows, c.rows);
    assert forall|j: int| 0 <= j < a.decls.len() implies a.decls[j] == c.decls[j] by {
        assert(a.decls[j] == b.decls[j]);
    }
    assert forall|k: int| 0 <= k < a.items.len() implies a.items[k] == c.items[k] by {
        assert(a.items[k] == b.items[k]);
    }
}

/// Nothing grows.
proof fn lemma_grows_same(o: Out)
    ensures
        out_grows(o, o),
{
}

/// Cutting the items of `f` back to those of `before`.
proof fn lemma_cut_items(before: Out, f: Out, n: Out)
    requires
        out_wf(f),
        out_grows(before, f),
        n.rows == f.rows,
        n.decls == f.decls,
        n.items == f.items.subrange(0, before.items.len() as int),
    ensures
        out_wf(n),
        out_grows(before, n),
        n.items == before.items,
{
    assert(n.items =~= before.items);
    assert forall|k: int| 0 <= k < n.items.len() implies #[trigger] item_wf(n, k) by {
        assert(item_wf(f, k));
        assert(n.items[k] == f.items[k]);
    }
}

/// The outermost rule goes on the end.
proof fn lemma_rule_finish(text: Seq<u32>, f: Out, n: Out, first: ExecItem, block: Block)
    requires
        out_wf(f),
        frame_ok(text, f.rows, first, block),
        first.start <= f.items.len(),
        !(block is Discard),
        n == (Out { rows: f.rows, decls: f.decls, items: f.items.push(first) }),
    ensures
        out_wf(n),
        out_grows(f, n),
        item_view(text, n, f.items.len() as int) == (BlockItem::Rule {
            rule: outcome(
                block,
                items_view(text, f, first.start as int, f.items.len() as int),
            ).unwrap(),
        }),
{
    let k = f.items.len() as int;
    assert forall|j: int| 0 <= j < f.items.len() implies f.items[j] == n.items[j] by {}
    assert forall|j: int| 0 <= j < f.rows.len() implies f.rows[j] == n.rows[j] by {}
    assert(n.items[k] == first);
    assert(out_grows(f, n));
    assert(item_wf(n, k));
    lemma_wf_grows(f, n);
    lemma_agree_items(text, f, n, first.start as int, k);
    lemma_frame_item(
        text,
        n,
        k,
        block,
        items_view(text, f, first.start as int, k),
    );
}

/// The item of an at-rule with no block.
proof fn lemma_statement_item(
    text: Seq<u32>,
    n: Out,
    k: int,
    name: Seq<u32>,
    prelude: Seq<ComponentValue>,
)
    requires
        0 <= k < n.items.len(),
        n.items[k].kind is StatementAtRule,
        token_value(
            ComponentValue::Token { token: token_at(text, false, n.items[k].pos as int) },
        ) == name,
        view_list(text, false, n.rows, n.items[k].lo as int, n.items[k].hi as int) == prelude,
    ensures
        item_view(text, n, k) == (BlockItem::Rule {
            rule: Rule::AtRule { name, prelude, child_rules: None },
        }),
{
}

/// How [`read_blocks`] starts.
#[derive(Clone, Copy)]
pub struct BlockStart {
    /// The position after the block's `{`.
    pub after_open: usize,
    /// The rule the block belongs to.
    pub first: ExecItem,
    /// True if nothing comes of the block.
    pub discard: bool,
}

/// "Consume a block" and the rule it makes, with `first` the rule. Every block inside goes
/// through the one loop: `stack` holds a rule for each block that is open.
pub fn read_blocks(
    text: &[u32],
    start: BlockStart,
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    items: &mut Vec<ExecItem>,
    Ghost(open): Ghost<int>,
    Ghost(block): Ghost<Block>,
) -> (r: (usize, Ghost<int>))
    requires
        text_fits(text@),
        at_index(text@, false, open + 1, start.after_open as int),
        start.after_open <= text.len(),
        is(next_token(stream_of(text@, false), open), Token::OpenCurly),
        start.first.start == old(items).len(),
        frame_ok(text@, old(rows)@, start.first, block),
        out_wf(out_of(old(rows)@, old(decls)@, old(items)@)),
        room(text@, old(rows).len() as nat, open + 1, start.after_open as int),
        budget(old(decls).len() as nat, old(items).len() as nat, 0, open),
        start.discard == (block is Discard),
    ensures
        ({
            let input = stream_of(text@, false);
            let (out, after) = block_result(input, open, block);
            let before = out_of(old(rows)@, old(decls)@, old(items)@);
            let new = out_of(final(rows)@, final(decls)@, final(items)@);
            &&& r.1@ == after
            &&& after > open
            &&& at_index(text@, false, after, r.0 as int)
            &&& start.after_open <= r.0 <= text.len()
            &&& out_wf(new)
            &&& out_grows(before, new)
            &&& room(text@, final(rows).len() as nat, after, r.0 as int)
            &&& budget(final(decls).len() as nat, final(items).len() as nat, 0, after)
            &&& start.discard ==> final(items)@ == old(items)@
            &&& !start.discard ==> final(items).len() > old(items).len()
            &&& !start.discard ==> final(items)@.last().start == old(items).len()
            &&& !start.discard ==> item_view(text@, new, final(items).len() - 1) == (BlockItem::Rule {
                rule: out.unwrap(),
            })
        }),
{
    let after_open = start.after_open;
    let first = start.first;
    let discard = start.discard;
    let ghost input = stream_of(text@, false);
    let ghost before = out_of(rows@, decls@, items@);
    let ghost target = block_result(input, open, block);
    let mut stack: Vec<ExecItem> = Vec::new();
    stack.push(first);
    let ghost mut frames = seq![RuleFrame { block, rules: Seq::empty(), decls: Seq::empty() }];
    let mut cur = decls.len();
    let mut at = after_open;
    let ghost mut idx = open + 1;
    proof {
        assert(stack@ =~= seq![first]);
        lemma_rule_start(text@, input, before, first, block, open);
        lemma_grows_same(before);
    }
    loop
        invariant
            text_fits(text@),
            input == stream_of(text@, false),
            target == block_result(input, open, block),
            at_index(text@, false, idx, at as int),
            after_open <= at <= text.len(),
            idx > open,
            rule_machine(
                text@,
                input,
                out_of(rows@, decls@, items@),
                stack@,
                frames,
                cur as int,
                idx,
                target,
            ),
            stack.len() == frames.len(),
            stack.len() > 0,
            stack@[0] == first,
            frames[0].block == block,
            before == out_of(old(rows)@, old(decls)@, old(items)@),
            out_grows(before, out_of(rows@, decls@, items@)),
            room(text@, rows.len() as nat, idx, at as int),
            budget(decls.len() as nat, items.len() as nat, stack.len() as nat, idx),
            cur <= decls.len(),
            discard == (block is Discard),
            first.start == old(items).len(),
            after_open == start.after_open,
            first == start.first,
            discard == start.discard,
        decreases 2 * tokens_left(text@, false, idx) + stack.len(),
    {
        let ghost o = out_of(rows@, decls@, items@);
        let ghost before_stack = stack@;
        let ghost before_frames = frames;
        let ghost before_idx = idx;
        let ghost before_cur = cur as int;
        let ghost top = frames.last();
        let ghost m = frames.len() as int;
        let (token, next) = read_token(text, false, at, Ghost(idx));
        if matches!(token, ExecToken::Whitespace) || matches!(token, ExecToken::Semicolon) {
            proof {
                lemma_rule_skip(text@, input, o, stack@, frames, cur as int, idx, target);
                idx = idx + 1;
            }
            at = next;
        } else if matches!(token, ExecToken::Eof) || matches!(token, ExecToken::CloseCurly) {
            flush_declarations(items, decls.len(), cur);
            let ghost f = out_of(rows@, decls@, items@);
            let frame = match stack.pop() {
                Some(frame) => frame,
                None => return (at, Ghost(idx)),
            };
            let end = if matches!(token, ExecToken::Eof) {
                at
            } else {
                next
            };
            proof {
                assert(before_stack.last() == frame);
            }
            if stack.is_empty() {
                proof {
                    assert(before_stack[0] == frame);
                    assert(before_frames.last() == before_frames[0]);
                    lemma_rule_done(
                        text@,
                        input,
                        o,
                        f,
                        before_stack,
                        before_frames,
                        before_cur,
                        before_idx,
                        target,
                    );
                    lemma_grows_chain(before, o, f);
                }
                if discard {
                    items.truncate(first.start as usize);
                    proof {
                        lemma_cut_items(before, f, out_of(rows@, decls@, items@));
                    }
                } else {
                    items.push(frame);
                    proof {
                        lemma_rule_finish(
                            text@,
                            f,
                            out_of(rows@, decls@, items@),
                            first,
                            block,
                        );
                        lemma_grows_chain(before, f, out_of(rows@, decls@, items@));
                    }
                }
                return (end, Ghost(target.1));
            }
            items.push(frame);
            proof {
                let n = out_of(rows@, decls@, items@);
                let rule = closed_rule(text@, o, before_frames, before_stack, before_cur);
                lemma_rule_close(
                    text@,
                    input,
                    o,
                    f,
                    n,
                    before_stack,
                    before_frames,
                    before_cur,
                    before_idx,
                    target,
                );
                lemma_grows_chain(before, o, n);
                assert(stack@ =~= before_stack.drop_last());
                frames = before_frames.drop_last().update(
                    m - 2,
                    RuleFrame {
                        block: before_frames[m - 2].block,
                        rules: before_frames[m - 2].rules.push(BlockItem::Rule { rule }),
                        decls: Seq::empty(),
                    },
                );
                idx = discard_a_token(input, before_idx);
            }
            cur = decls.len();
            at = end;
        } else if matches!(token, ExecToken::AtKeyword { .. }) {
            let (done, end, Ghost(after), head) = read_at_head(text, at, true, rows, Ghost(idx));
            let ghost o1 = out_of(rows@, decls@, items@);
            let ghost name = at_name(input, before_idx);
            let ghost prelude = view_list(
                text@,
                false,
                rows@,
                head.lo as int,
                rows.len() as int,
            );
            proof {
                lemma_rule_rows(
                    text@,
                    input,
                    o,
                    o1,
                    before_stack,
                    before_frames,
                    before_cur,
                    before_idx,
                    target,
                );
            }
            flush_declarations(items, decls.len(), cur);
            let ghost f = out_of(rows@, decls@, items@);
            let start = items.len() as u32;
            let item = ExecItem { kind: head.kind, pos: head.pos, start, lo: head.lo, hi: head.hi };
            if done {
                items.push(item);
                proof {
                    let n = out_of(rows@, decls@, items@);
                    let rule = Rule::AtRule { name, prelude, child_rules: None };
                    assert(items@.drop_last() =~= f.items);
                    lemma_statement_item(text@, n, f.items.len() as int, name, prelude);
                    lemma_rule_statement(
                        text@,
                        input,
                        o1,
                        f,
                        n,
                        before_stack,
                        before_frames,
                        before_cur,
                        before_idx,
                        target,
                        rule,
                        after,
                    );
                    lemma_grows_chain(before, o, o1);
                    lemma_grows_chain(before, o1, n);
                    frames = before_frames.update(
                        m - 1,
                        RuleFrame {
                            block: top.block,
                            rules: with_declarations(top.rules, top.decls).push(
                                BlockItem::Rule { rule },
                            ),
                            decls: Seq::empty(),
                        },
                    );
                    idx = after;
                }
            } else {
                stack.push(item);
                proof {
                    let child = Block::AtRule { name, prelude };
                    let result = block_result(input, after, child);
                    lemma_contents_at(input, top, before_idx, result.0.unwrap(), result.1);
                    lemma_rule_push(
                        text@,
                        input,
                        o1,
                        f,
                        before_stack,
                        before_frames,
                        before_cur,
                        before_idx,
                        target,
                        item,
                        child,
                        after,
                    );
                    lemma_grows_chain(before, o, o1);
                    lemma_grows_chain(before, o1, f);
                    frames = before_frames.update(
                        m - 1,
                        RuleFrame {
                            block: top.block,
                            rules: with_declarations(top.rules, top.decls),
                            decls: Seq::empty(),
                        },
                    ).push(RuleFrame { block: child, rules: Seq::empty(), decls: Seq::empty() });
                    idx = after + 1;
                }
            }
            cur = decls.len();
            at = end;
        } else {
            let (found, end, Ghost(after)) = read_declaration(
                text,
                at,
                true,
                true,
                rows,
                decls,
                Ghost(idx),
            );
            if found {
                proof {
                    let n = out_of(rows@, decls@, items@);
                    let decl = consume_a_declaration(input, before_idx, true).0.unwrap();
                    lemma_rule_declaration(
                        text@,
                        input,
                        o,
                        n,
                        before_stack,
                        before_frames,
                        before_cur,
                        before_idx,
                        target,
                        decl,
                        after,
                    );
                    lemma_grows_chain(before, o, n);
                    frames = before_frames.update(
                        m - 1,
                        RuleFrame {
                            block: top.block,
                            rules: top.rules,
                            decls: top.decls.push(decl),
                        },
                    );
                    idx = after;
                }
                at = end;
            } else {
                let lo = rows.len();
                let (status, end2, Ghost(after2)) = read_qualified_head(
                    text,
                    at,
                    1,
                    true,
                    rows,
                    Ghost(idx),
                );
                if status == 0 {
                    proof {
                        lemma_rule_nothing(
                            text@,
                            input,
                            o,
                            before_stack,
                            before_frames,
                            before_cur,
                            before_idx,
                            target,
                            after2,
                        );
                        idx = after2;
                    }
                    at = end2;
                } else {
                    let ghost o1 = out_of(rows@, decls@, items@);
                    let ghost prelude = view_list(
                        text@,
                        false,
                        rows@,
                        lo as int,
                        rows.len() as int,
                    );
                    proof {
                        lemma_rule_rows(
                            text@,
                            input,
                            o,
                            o1,
                            before_stack,
                            before_frames,
                            before_cur,
                            before_idx,
                            target,
                        );
                    }
                    flush_declarations(items, decls.len(), cur);
                    let ghost f = out_of(rows@, decls@, items@);
                    let start = items.len() as u32;
                    let item = ExecItem {
                        kind: ExecItemKind::QualifiedRule,
                        pos: 0,
                        start,
                        lo: lo as u32,
                        hi: rows.len() as u32,
                    };
                    stack.push(item);
                    proof {
                        let child = Block::QualifiedRule { prelude };
                        let result = block_result(input, after2, child);
                        lemma_contents_qualified(
                            input,
                            top,
                            before_idx,
                            result.0.unwrap(),
                            result.1,
                        );
                        lemma_rule_push(
                            text@,
                            input,
                            o1,
                            f,
                            before_stack,
                            before_frames,
                            before_cur,
                            before_idx,
                            target,
                            item,
                            child,
                            after2,
                        );
                        lemma_grows_chain(before, o, o1);
                        lemma_grows_chain(before, o1, f);
                        frames = before_frames.update(
                            m - 1,
                            RuleFrame {
                                block: top.block,
                                rules: with_declarations(top.rules, top.decls),
                                decls: Seq::empty(),
                            },
                        ).push(RuleFrame { block: child, rules: Seq::empty(), decls: Seq::empty() });
                        idx = after2 + 1;
                    }
                    cur = decls.len();
                    at = end2;
                }
            }
        }
    }
}

} // verus!
