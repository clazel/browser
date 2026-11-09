//! The component values a selector is parsed from, read out of `clazel-css`'s rows.
//!
//! "Parse a list of component values" gives flat rows (`clazel_css::parser::rows`), each a
//! position in the text where reading gives its token again. The grammar wants a list it can
//! index, so a list's rows are read once, in order, into [`ExecItem`]s, each proven to be the
//! component value the spec has at that index.

#[allow(unused_imports)]
use super::contract::*;
use super::exec_types::item;
#[allow(unused_imports)]
use super::spec::*;
use clazel_css::parser::exec_parse::ExecParsed;
use clazel_css::tokenizer::exec::ExecToken;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One component value of a list.
#[derive(Debug)]
pub enum ExecItem {
    /// A token that opens nothing.
    Token {
        /// The token.
        token: ExecToken,
    },
    /// A function: its name, and its value, the rows `lo` up to `hi`.
    Function {
        /// The name.
        name: Vec<u32>,
        /// The first row of its value.
        lo: usize,
        /// The row after its value.
        hi: usize,
    },
    /// A simple block: its opening token, and its value, the rows `lo` up to `hi`.
    Block {
        /// The opening token.
        token: ExecToken,
        /// The first row of its value.
        lo: usize,
        /// The row after its value.
        hi: usize,
    },
}

/// The component values of rows `lo` up to `hi` of a parse.
pub open spec fn rows_list(src: ExecParsed, lo: int, hi: int) -> Seq<ComponentValue> {
    clazel_css::parser::rows::view_list(src.text@, false, src.output.rows@, lo, hi)
}

/// The component value of row `k`.
pub open spec fn row_value(src: ExecParsed, k: int) -> ComponentValue {
    clazel_css::parser::rows::view_value(src.text@, false, src.output.rows@, k)
}

/// What reading the text again needs of a parse.
pub open spec fn src_ok(src: ExecParsed) -> bool {
    clazel_css::parser::exec_rules::text_fits(src.text@)
}

/// True if `it` is the component value `v`.
pub open spec fn item_is(src: ExecParsed, it: ExecItem, v: ComponentValue) -> bool {
    match it {
        ExecItem::Token { token } => v == ComponentValue::Token {
            token: clazel_css::tokenizer::exec::view_token(token),
        },
        ExecItem::Function { name, lo, hi } => v == ComponentValue::Function {
            name: name@,
            value: rows_list(src, lo as int, hi as int),
        },
        ExecItem::Block { token, lo, hi } => v == ComponentValue::SimpleBlock {
            associated_token: clazel_css::tokenizer::exec::view_token(token),
            value: rows_list(src, lo as int, hi as int),
        },
    }
}

/// True if `items` are the list `list`.
pub open spec fn items_are(src: ExecParsed, items: Seq<ExecItem>, list: Seq<ComponentValue>) -> bool {
    items.len() == list.len() && forall|j: int| 0 <= j < items.len() ==> #[trigger] item_is(src, items[j], list[j])
}

/// Past the end of the text, reading gives the EOF token.
proof fn lemma_eof_past_end(text: Seq<u32>, pos: int)
    requires
        pos >= text.len(),
    ensures
        clazel_css::tokenizer::spec::consume_a_token(text, pos, false).0 == Token::Eof,
{
    assert(clazel_css::tokenizer::spec::at(text, pos) == clazel_css::tokenizer::spec::EOF);
    assert(clazel_css::tokenizer::spec::consume_comments(text, pos) == pos);
}

/// The token reading gives at row `k`.
fn row_token(src: &ExecParsed, k: usize) -> (r: ExecToken)
    requires
        src_ok(*src),
        k < src.output.rows@.len(),
    ensures
        clazel_css::tokenizer::exec::view_token(r) == clazel_css::parser::rows::token_at(
            src.text@,
            false,
            src.output.rows@[k as int].pos as int,
        ),
{
    let pos = item(src.output.rows.as_slice(), k).pos as usize;
    if pos <= src.text.len() {
        let (token, _) = clazel_css::tokenizer::exec::next_token(src.text.as_slice(), pos, false);
        token
    } else {
        proof {
            lemma_eof_past_end(src.text@, pos as int);
        }
        ExecToken::Eof
    }
}

/// The component value of row `k`.
fn read_item(src: &ExecParsed, k: usize) -> (r: ExecItem)
    requires
        src_ok(*src),
        k < src.output.rows@.len(),
    ensures
        item_is(*src, r, row_value(*src, k as int)),
{
    let token = row_token(src, k);
    let start = item(src.output.rows.as_slice(), k).start as usize;
    match token {
        ExecToken::Function { value } => ExecItem::Function { name: value, lo: start, hi: k },
        ExecToken::OpenCurly => ExecItem::Block { token: ExecToken::OpenCurly, lo: start, hi: k },
        ExecToken::OpenSquare => ExecItem::Block { token: ExecToken::OpenSquare, lo: start, hi: k },
        ExecToken::OpenParen => ExecItem::Block { token: ExecToken::OpenParen, lo: start, hi: k },
        other => ExecItem::Token { token: other },
    }
}

/// The component values of rows `lo` up to `hi`, in order.
pub fn read_items(src: &ExecParsed, lo: usize, hi: usize) -> (r: Vec<ExecItem>)
    requires
        src_ok(*src),
    ensures
        items_are(*src, r@, rows_list(*src, lo as int, hi as int)),
{
    let ghost text = src.text@;
    let ghost rows = src.output.rows@;
    let ghost whole = rows_list(*src, lo as int, hi as int);
    // Walk from the end, as the view does, keeping the rows met; then read them in order.
    let mut met: Vec<usize> = Vec::new();
    let mut cur = hi;
    loop
        invariant_except_break
            text == src.text@,
            rows == src.output.rows@,
            whole == rows_list(*src, lo as int, hi as int),
            whole.len() == rows_list(*src, lo as int, cur as int).len() + met@.len(),
            forall|j: int| 0 <= j < rows_list(*src, lo as int, cur as int).len() ==> #[trigger] whole[j] == rows_list(*src, lo as int, cur as int)[j],
            forall|j: int|
                0 <= j < met@.len() ==> #[trigger] met@[j] < rows.len() && whole[whole.len() - 1 - j]
                    == row_value(*src, met@[j] as int),
        ensures
            whole.len() == met@.len(),
            forall|j: int|
                0 <= j < met@.len() ==> #[trigger] met@[j] < rows.len() && whole[whole.len() - 1 - j]
                    == row_value(*src, met@[j] as int),
        decreases cur,
    {
        if cur <= lo || cur > src.output.rows.len() {
            break;
        }
        let last = cur.saturating_sub(1);
        let start = item(src.output.rows.as_slice(), last).start as usize;
        if start >= cur {
            break;
        }
        let ghost before = rows_list(*src, lo as int, cur as int);
        proof {
            assert(before == rows_list(*src, lo as int, start as int).push(row_value(*src, last as int)));
        }
        met.push(last);
        cur = start;
    }
    let mut out: Vec<ExecItem> = Vec::new();
    let mut j = met.len();
    while j > 0
        invariant
            j <= met@.len(),
            whole.len() == met@.len(),
            src_ok(*src),
            forall|i: int|
                0 <= i < met@.len() ==> #[trigger] met@[i] < src.output.rows@.len() && whole[whole.len() - 1 - i]
                    == row_value(*src, met@[i] as int),
            out@.len() == met@.len() - j,
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] item_is(*src, out@[i], whole[i]),
        decreases j,
    {
        j = j.saturating_sub(1);
        let k = *item(met.as_slice(), j);
        let it = read_item(src, k);
        proof {
            assert(whole[whole.len() - 1 - j] == row_value(*src, k as int));
            assert(out@.len() == whole.len() - 1 - j);
        }
        out.push(it);
    }
    out
}

} // verus!
