//! The parser's entry points, proven to meet [`super::contract`]. Each takes the code points
//! of a string, runs "filter code points", and reads in lockstep.

#[allow(unused_imports)]
use super::contract::*;
use super::exec::*;
use super::exec_declaration::*;
use super::exec_lists::*;
use super::exec_rules::*;
use super::rows::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Filtering never makes a string longer.
proof fn lemma_filter_len(input: Seq<u32>, pos: int, output: Seq<u32>)
    requires
        pos >= 0,
    ensures
        crate::tokenizer::spec::filter_loop(input, pos, output).len() <= output.len() + remaining(
            input,
            pos,
        ),
    decreases remaining(input, pos),
{
    if pos < input.len() {
        let c = input[pos];
        if c == 0x0D && crate::tokenizer::spec::at(input, pos + 1) == 0x0A {
            lemma_filter_len(input, pos + 2, output.push(0x0A));
        } else if c == 0x0D || c == 0x0C {
            lemma_filter_len(input, pos + 1, output.push(0x0A));
        } else if c == 0 || crate::tokenizer::spec::is_surrogate(c as nat) {
            lemma_filter_len(input, pos + 1, output.push(crate::tokenizer::spec::REPLACEMENT));
        } else {
            lemma_filter_len(input, pos + 1, output.push(c));
        }
    }
}

/// "Filter code points", with what reading the result needs of it.
fn filtered(input: &[u32]) -> (text: Vec<u32>)
    requires
        parser_input_requires(input@),
    ensures
        text@ == filter_code_points(input@),
        text_fits(text@),
{
    let text = crate::tokenizer::exec::filter(input);
    proof {
        lemma_filter_len(input@, 0, Seq::empty());
        crate::tokenizer::lemmas::lemma_loop_bounded(text@, 0, false, Seq::empty());
        assert(text@ == filter_code_points(input@));
    }
    text
}

/// The start of reading, in the terms the readers ask for.
proof fn lemma_start(text: Seq<u32>)
    requires
        text_fits(text),
    ensures
        at_index(text, false, 0, 0),
        room(text, 0, 0, 0),
        out_wf(out_of(Seq::empty(), Seq::empty(), Seq::empty())),
        budget(0, 0, 0, 0),
{
    lemma_at_start(text, false);
}

/// A rule's item went on the end of the items.
proof fn lemma_item_pushed(text: Seq<u32>, o: Out, n: Out, lo: int)
    requires
        out_wf(o),
        out_grows(o, n),
        0 <= lo <= o.items.len(),
        n.items.len() > o.items.len(),
        n.items.last().start == o.items.len(),
    ensures
        items_view(text, n, lo, n.items.len() as int) == items_view(
            text,
            o,
            lo,
            o.items.len() as int,
        ).push(item_view(text, n, n.items.len() - 1)),
{
    assert(n.items[n.items.len() - 1] == n.items.last());
    lemma_agree_items(text, o, n, lo, o.items.len() as int);
}

/// [`child_rules_of`] of one more rule.
proof fn lemma_child_rules_push(items: Seq<BlockItem>, rule: Rule)
    ensures
        child_rules_of(items.push(BlockItem::Rule { rule })) == child_rules_of(items).push(rule),
{
    assert(child_rules_of(items.push(BlockItem::Rule { rule })) =~= child_rules_of(items).push(
        rule,
    ));
}

/// Only rows were added.
proof fn lemma_rows_grew(o: Out, n: Out)
    requires
        out_wf(o),
        extends(o.rows, n.rows),
        o.rows.len() <= n.rows.len(),
        n.decls == o.decls,
        n.items == o.items,
    ensures
        out_wf(n),
        out_grows(o, n),
{
    assert(out_grows(o, n));
    lemma_wf_grows(o, n);
}

/// "Consume an at-rule", not nested.
fn read_at_rule(
    text: &[u32],
    pos: usize,
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    items: &mut Vec<ExecItem>,
    Ghost(index): Ghost<int>,
) -> (r: (usize, Ghost<int>))
    requires
        text_fits(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        is_at_keyword(next_token(stream_of(text@, false), index)),
        room(text@, old(rows).len() as nat, index, pos as int),
        out_wf(out_of(old(rows)@, old(decls)@, old(items)@)),
        budget(old(decls).len() as nat, old(items).len() as nat, 0, index),
    ensures
        ({
            let input = stream_of(text@, false);
            let (rule, after) = consume_an_at_rule(input, index, false);
            let new = out_of(final(rows)@, final(decls)@, final(items)@);
            &&& r.1@ == after
            &&& after > index
            &&& rule is Some
            &&& at_index(text@, false, after, r.0 as int)
            &&& pos <= r.0 <= text.len()
            &&& out_wf(new)
            &&& out_grows(out_of(old(rows)@, old(decls)@, old(items)@), new)
            &&& room(text@, final(rows).len() as nat, after, r.0 as int)
            &&& budget(final(decls).len() as nat, final(items).len() as nat, 0, after)
            &&& final(items).len() > old(items).len()
            &&& final(items)@.last().start == old(items).len()
            &&& item_view(text@, new, final(items).len() - 1) == (BlockItem::Rule {
                rule: rule.unwrap(),
            })
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost o = out_of(rows@, decls@, items@);
    let (done, end, Ghost(after), head) = read_at_head(text, pos, false, rows, Ghost(index));
    let ghost o1 = out_of(rows@, decls@, items@);
    let ghost name = at_name(input, index);
    let ghost prelude = view_list(text@, false, rows@, head.lo as int, rows.len() as int);
    let start = items.len() as u32;
    let item = ExecItem { kind: head.kind, pos: head.pos, start, lo: head.lo, hi: head.hi };
    proof {
        lemma_rows_grew(o, o1);
    }
    if done {
        items.push(item);
        proof {
            let n = out_of(rows@, decls@, items@);
            let k = o1.items.len() as int;
            assert forall|j: int| 0 <= j < o1.items.len() implies o1.items[j] == n.items[j] by {}
            assert forall|j: int| 0 <= j < o1.rows.len() implies o1.rows[j] == n.rows[j] by {}
            assert(out_grows(o1, n));
            assert(n.items[k] == item);
            assert(item_wf(n, k));
            lemma_wf_grows(o1, n);
            lemma_grows_chain(o, o1, n);
        }
        (end, Ghost(after))
    } else {
        let (finish, Ghost(next)) = read_blocks(
            text,
            end,
            item,
            false,
            rows,
            decls,
            items,
            Ghost(after),
            Ghost(Block::AtRule { name, prelude }),
        );
        proof {
            lemma_grows_chain(o, o1, out_of(rows@, decls@, items@));
        }
        (finish, Ghost(next))
    }
}

/// "Consume a qualified rule", not nested, with no stop token. The first result says
/// whether it gave a rule.
fn read_qualified_rule(
    text: &[u32],
    pos: usize,
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    items: &mut Vec<ExecItem>,
    Ghost(index): Ghost<int>,
) -> (r: (bool, usize, Ghost<int>))
    requires
        text_fits(text@),
        at_index(text@, false, index, pos as int),
        pos <= text.len(),
        !is_empty(stream_of(text@, false), index),
        !is_at_keyword(next_token(stream_of(text@, false), index)),
        room(text@, old(rows).len() as nat, index, pos as int),
        out_wf(out_of(old(rows)@, old(decls)@, old(items)@)),
        budget(old(decls).len() as nat, old(items).len() as nat, 0, index),
    ensures
        ({
            let input = stream_of(text@, false);
            let (result, after) = consume_a_qualified_rule(input, index, None, false);
            let new = out_of(final(rows)@, final(decls)@, final(items)@);
            &&& r.2@ == after
            &&& after > index
            &&& r.0 == (result is Rule)
            &&& at_index(text@, false, after, r.1 as int)
            &&& pos <= r.1 <= text.len()
            &&& out_wf(new)
            &&& out_grows(out_of(old(rows)@, old(decls)@, old(items)@), new)
            &&& room(text@, final(rows).len() as nat, after, r.1 as int)
            &&& budget(final(decls).len() as nat, final(items).len() as nat, 0, after)
            &&& !r.0 ==> final(items)@ == old(items)@
            &&& r.0 ==> final(items).len() > old(items).len()
            &&& r.0 ==> final(items)@.last().start == old(items).len()
            &&& r.0 ==> item_view(text@, new, final(items).len() - 1) == (BlockItem::Rule {
                rule: as_option(result).unwrap(),
            })
        }),
{
    let ghost input = stream_of(text@, false);
    let ghost o = out_of(rows@, decls@, items@);
    let lo = rows.len();
    proof {
        super::termination::theorem_stylesheet_moves(input, index);
    }
    let (status, end, Ghost(after)) = read_qualified_head(text, pos, 0, false, rows, Ghost(index));
    let ghost o1 = out_of(rows@, decls@, items@);
    let ghost prelude = view_list(text@, false, rows@, lo as int, rows.len() as int);
    proof {
        lemma_rows_grew(o, o1);
    }
    if status == 0 {
        return (false, end, Ghost(after));
    }
    let start = items.len() as u32;
    let item = ExecItem {
        kind: ExecItemKind::QualifiedRule,
        pos: 0,
        start,
        lo: lo as u32,
        hi: rows.len() as u32,
    };
    let (finish, Ghost(next)) = if status == 1 {
        read_blocks(
            text,
            end,
            item,
            false,
            rows,
            decls,
            items,
            Ghost(after),
            Ghost(Block::QualifiedRule { prelude }),
        )
    } else {
        read_blocks(
            text,
            end,
            item,
            true,
            rows,
            decls,
            items,
            Ghost(after),
            Ghost(Block::Discard),
        )
    };
    proof {
        lemma_grows_chain(o, o1, out_of(rows@, decls@, items@));
    }
    (status == 1, finish, Ghost(next))
}

/// "Consume a stylesheet's contents".
fn read_stylesheet_contents(
    text: &[u32],
    rows: &mut Vec<ExecRow>,
    decls: &mut Vec<ExecDeclaration>,
    items: &mut Vec<ExecItem>,
)
    requires
        text_fits(text@),
        old(rows).len() == 0,
        old(decls).len() == 0,
        old(items).len() == 0,
    ensures
        view_rules(text@, final(rows)@, final(decls)@, final(items)@)
            == consume_a_stylesheets_contents(stream_of(text@, false), 0).0,
{
    let ghost input = stream_of(text@, false);
    let ghost target = consume_a_stylesheets_contents(input, 0);
    let mut at: usize = 0;
    let ghost mut idx: int = 0;
    proof {
        lemma_start(text@);
        let o = out_of(rows@, decls@, items@);
        assert(rows@ =~= Seq::<ExecRow>::empty());
        assert(decls@ =~= Seq::<ExecDeclaration>::empty());
        assert(items@ =~= Seq::<ExecItem>::empty());
        assert(child_rules_of(items_view(text@, o, 0, 0)) =~= Seq::<Rule>::empty());
    }
    loop
        invariant
            text_fits(text@),
            input == stream_of(text@, false),
            at_index(text@, false, idx, at as int),
            at <= text.len(),
            idx >= 0,
            room(text@, rows.len() as nat, idx, at as int),
            out_wf(out_of(rows@, decls@, items@)),
            budget(decls.len() as nat, items.len() as nat, 0, idx),
            stylesheets_contents_loop(
                input,
                idx,
                child_rules_of(
                    items_view(text@, out_of(rows@, decls@, items@), 0, items.len() as int),
                ),
            ) == target,
            target == consume_a_stylesheets_contents(input, 0),
        decreases tokens_left(text@, false, idx),
    {
        let ghost o = out_of(rows@, decls@, items@);
        let ghost list = items_view(text@, o, 0, items.len() as int);
        let ghost before = idx;
        let (token, next) = read_token(text, false, at, Ghost(idx));
        if matches!(token, ExecToken::Eof) {
            return;
        } else if matches!(token, ExecToken::Whitespace) || matches!(token, ExecToken::Cdo)
            || matches!(token, ExecToken::Cdc) {
            at = next;
            proof {
                idx = idx + 1;
            }
        } else if matches!(token, ExecToken::AtKeyword { .. }) {
            let (end, Ghost(after)) = read_at_rule(text, at, rows, decls, items, Ghost(idx));
            proof {
                let n = out_of(rows@, decls@, items@);
                let rule = consume_an_at_rule(input, before, false).0.unwrap();
                lemma_item_pushed(text@, o, n, 0);
                lemma_child_rules_push(list, rule);
                idx = after;
            }
            at = end;
        } else {
            let (pushed, end, Ghost(after)) = read_qualified_rule(
                text,
                at,
                rows,
                decls,
                items,
                Ghost(idx),
            );
            proof {
                let n = out_of(rows@, decls@, items@);
                let result = consume_a_qualified_rule(input, before, None, false).0;
                if pushed {
                    let rule = as_option(result).unwrap();
                    lemma_item_pushed(text@, o, n, 0);
                    lemma_child_rules_push(list, rule);
                } else {
                    lemma_agree_items(text@, o, n, 0, o.items.len() as int);
                }
                idx = after;
            }
            at = end;
        }
    }
}

/// The result of a parse, and the text its rows are positions in.
pub struct ExecParsed {
    /// The string after "filter code points".
    pub text: Vec<u32>,
    /// The arrays.
    pub output: ExecOutput,
}

/// "Parse a stylesheet's contents" of `input`.
pub fn parse_stylesheet_contents(input: &[u32]) -> (r: ExecParsed)
    requires
        parser_input_requires(input@),
    ensures
        parse_stylesheet_contents_ensures(
            input@,
            view_rules(
                r.text@,
                r.output.rows@,
                r.output.declarations@,
                r.output.items@,
            ),
        ),
{
    let text = filtered(input);
    let mut rows: Vec<ExecRow> = Vec::new();
    let mut declarations: Vec<ExecDeclaration> = Vec::new();
    let mut items: Vec<ExecItem> = Vec::new();
    read_stylesheet_contents(text.as_slice(), &mut rows, &mut declarations, &mut items);
    ExecParsed { text, output: ExecOutput { rows, declarations, items } }
}

/// "Parse a stylesheet" of `input`. The location is the caller's to keep: nothing here reads
/// it.
pub fn parse_stylesheet(input: &[u32], Ghost(location): Ghost<Option<Seq<u32>>>) -> (r: ExecParsed)
    requires
        parser_input_requires(input@),
    ensures
        parse_stylesheet_ensures(
            input@,
            location,
            Stylesheet {
                location,
                rules: view_rules(
                    r.text@,
                    r.output.rows@,
                    r.output.declarations@,
                    r.output.items@,
                ),
            },
        ),
{
    parse_stylesheet_contents(input)
}

} // verus!
