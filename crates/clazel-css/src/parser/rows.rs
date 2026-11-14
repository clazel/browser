//! What the exec parser builds, and what each piece means in terms of [`super::spec`].
//!
//! The spec's results are trees. The exec parser's are flat arrays, because a tree of
//! `Vec`s nested a million deep would overflow the stack when dropped, and would cost far
//! more than the sheet. Nothing is stored that the input already says: a row keeps where a
//! token is, and reading there gives the token again, which `theorem_reader` proves is the
//! token the spec has.
//!
//! Every array is in post-order and only ever grows at its end: a block's row comes after
//! the rows inside it. Each view walks from the end, as `Seq::push` builds, so appending a
//! row is one step of the view and no row is ever changed.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One component value. Which kind it is comes from the token at `pos`: a function token or
/// an opening bracket is a function or a simple block, and anything else is that token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecRow {
    /// Where reading gives this value's token, or its opening token. It is the end of the
    /// token before, so any comments are still ahead of it.
    pub pos: u32,
    /// The first row of this value: its own row, or the first row inside it. The value
    /// before this one in a list is the row before that.
    pub start: u32,
}

/// The token at `pos`.
pub open spec fn token_at(text: Seq<u32>, flag: bool, pos: int) -> Token {
    read_a_token(text, pos, flag).0
}

/// True if reading gives something that holds a list of values.
pub open spec fn opens_a_value(token: Token) -> bool {
    token is Function || token is OpenCurly || token is OpenSquare || token is OpenParen
}

/// The component value of row `k`.
pub open spec fn view_value(text: Seq<u32>, flag: bool, rows: Seq<ExecRow>, k: int) -> ComponentValue
    decreases k + 1, 0int,
{
    if k < 0 || k >= rows.len() {
        ComponentValue::Token { token: Token::Eof }
    } else {
        let token = token_at(text, flag, rows[k].pos as int);
        match token {
            Token::Function { value } => ComponentValue::Function {
                name: value,
                value: view_list(text, flag, rows, rows[k].start as int, k),
            },
            Token::OpenCurly => ComponentValue::SimpleBlock {
                associated_token: token,
                value: view_list(text, flag, rows, rows[k].start as int, k),
            },
            Token::OpenSquare => ComponentValue::SimpleBlock {
                associated_token: token,
                value: view_list(text, flag, rows, rows[k].start as int, k),
            },
            Token::OpenParen => ComponentValue::SimpleBlock {
                associated_token: token,
                value: view_list(text, flag, rows, rows[k].start as int, k),
            },
            _ => ComponentValue::Token { token },
        }
    }
}

/// The list of values in rows `lo` up to `hi`.
pub open spec fn view_list(
    text: Seq<u32>,
    flag: bool,
    rows: Seq<ExecRow>,
    lo: int,
    hi: int,
) -> Seq<ComponentValue>
    decreases hi, 1int,
{
    if lo < 0 || hi <= lo || hi > rows.len() || rows[hi - 1].start >= hi {
        Seq::empty()
    } else {
        view_list(text, flag, rows, lo, rows[hi - 1].start as int).push(
            view_value(text, flag, rows, hi - 1),
        )
    }
}

/// Which of the text's three ways a declaration ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecDeclarationKind {
    /// No original text, and the value is what the rows say.
    Plain,
    /// "decl's name is a custom property name string": it has an original text.
    Custom,
    /// "decl's name is an ASCII case-insensitive match for "unicode-range"": the rows of the
    /// value are positions in the segment, read with unicode ranges allowed.
    UnicodeRange,
}

/// One declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecDeclaration {
    /// Where reading gives the `<ident-token>` of its name.
    pub name_pos: u32,
    /// The first row of its value.
    pub value_lo: u32,
    /// The row after its value.
    pub value_hi: u32,
    /// The important flag.
    pub important: bool,
    /// What its value is.
    pub kind: ExecDeclarationKind,
    /// Where its original text, or its unicode-range segment, starts.
    pub text_start: u32,
    /// Where that ends.
    pub text_end: u32,
}

/// The declaration `decl`.
pub open spec fn view_declaration(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    decl: ExecDeclaration,
) -> Declaration {
    let name = token_value(
        ComponentValue::Token { token: token_at(text, false, decl.name_pos as int) },
    );
    let segment = text.subrange(decl.text_start as int, decl.text_end as int);
    let lo = decl.value_lo as int;
    let hi = decl.value_hi as int;
    match decl.kind {
        ExecDeclarationKind::Plain => Declaration {
            name,
            value: view_list(text, false, rows, lo, hi),
            important: decl.important,
            original_text: None,
        },
        ExecDeclarationKind::Custom => Declaration {
            name,
            value: view_list(text, false, rows, lo, hi),
            important: decl.important,
            original_text: Some(segment),
        },
        ExecDeclarationKind::UnicodeRange => Declaration {
            name,
            value: view_list(segment, true, rows, lo, hi),
            important: decl.important,
            original_text: None,
        },
    }
}

/// Declarations `lo` up to `hi`.
pub open spec fn view_declarations(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    decls: Seq<ExecDeclaration>,
    lo: int,
    hi: int,
) -> Seq<Declaration> {
    Seq::new(
        if hi > lo {
            (hi - lo) as nat
        } else {
            0
        },
        |i: int| view_declaration(text, rows, decls[lo + i]),
    )
}

/// What an item of a block is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecItemKind {
    /// A statement at-rule: `lo` and `hi` are the rows of its prelude.
    StatementAtRule,
    /// A block at-rule: the prelude as above, and its block's items before this one.
    BlockAtRule,
    /// A qualified rule: likewise.
    QualifiedRule,
    /// A list of declarations: `lo` and `hi` are places in the declarations.
    Declarations,
}

/// One item of "consume a block's contents", or one rule of a stylesheet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecItem {
    /// What it is.
    pub kind: ExecItemKind,
    /// An at-rule's name: where reading gives its `<at-keyword-token>`.
    pub pos: u32,
    /// The first item of this one: itself, or the first item of its block.
    pub start: u32,
    /// See [`ExecItemKind`].
    pub lo: u32,
    /// See [`ExecItemKind`].
    pub hi: u32,
}

/// What a parse gives, apart from the text it read.
pub struct ExecOutput {
    /// The component values.
    pub rows: Vec<ExecRow>,
    /// The declarations.
    pub declarations: Vec<ExecDeclaration>,
    /// The rules and lists of declarations.
    pub items: Vec<ExecItem>,
}

/// The item at `k`.
pub open spec fn view_item(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    decls: Seq<ExecDeclaration>,
    items: Seq<ExecItem>,
    k: int,
) -> BlockItem
    decreases k + 1, 0int,
{
    if k < 0 || k >= items.len() {
        BlockItem::Declarations { declarations: Seq::empty() }
    } else {
        let item = items[k];
        let prelude = view_list(text, false, rows, item.lo as int, item.hi as int);
        let name = token_value(
            ComponentValue::Token { token: token_at(text, false, item.pos as int) },
        );
        match item.kind {
            ExecItemKind::StatementAtRule => BlockItem::Rule {
                rule: Rule::AtRule { name, prelude, child_rules: None },
            },
            ExecItemKind::BlockAtRule => BlockItem::Rule {
                rule: Rule::AtRule {
                    name,
                    prelude,
                    child_rules: Some(view_items(text, rows, decls, items, item.start as int, k)),
                },
            },
            ExecItemKind::QualifiedRule => BlockItem::Rule {
                rule: qualified_rule_from(
                    prelude,
                    view_items(text, rows, decls, items, item.start as int, k),
                ),
            },
            ExecItemKind::Declarations => BlockItem::Declarations {
                declarations: view_declarations(
                    text,
                    rows,
                    decls,
                    item.lo as int,
                    item.hi as int,
                ),
            },
        }
    }
}

/// The items `lo` up to `hi`.
pub open spec fn view_items(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    decls: Seq<ExecDeclaration>,
    items: Seq<ExecItem>,
    lo: int,
    hi: int,
) -> Seq<BlockItem>
    decreases hi, 1int,
{
    if lo < 0 || hi <= lo || hi > items.len() || items[hi - 1].start >= hi {
        Seq::empty()
    } else {
        view_items(text, rows, decls, items, lo, items[hi - 1].start as int).push(
            view_item(text, rows, decls, items, hi - 1),
        )
    }
}

/// The rules of a stylesheet's items, all of which are rules.
pub open spec fn view_rules(
    text: Seq<u32>,
    rows: Seq<ExecRow>,
    decls: Seq<ExecDeclaration>,
    items: Seq<ExecItem>,
) -> Seq<Rule> {
    child_rules_of(view_items(text, rows, decls, items, 0, items.len() as int))
}

} // verus!
