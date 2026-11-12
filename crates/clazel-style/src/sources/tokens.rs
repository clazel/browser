//! The component values a media query list is read from, flattened.
//!
//! Media Queries 4 §3 reads a `<media-query-list>` from component values, as CSS Syntax 3
//! §5.4 parses them, the way [`crate::values::items`] reads a property's value. Its grammar
//! needs three things that flattening drops: whitespace (no whitespace may come between `<`
//! or `>` and a following `=`, §3), the colon of `<mf-plain>`, and which bracket a simple
//! block has (only `( … )` is `<media-in-parens>`). So this is its own flattening, in the
//! same shape: [`Tok`]s in pre-order, a block or function followed by its contents, with
//! the index after them as its `end`, and every string a [`Span`] of one text.
//!
//! As in `values/items.rs`, nothing assumes the tokens are well formed: the parser clamps
//! every `end` to the list it is in, so the Kani harnesses can run it on any tokens.

use clazel_css::parser::contract::MAX_PARSER_INPUT;
use clazel_css::parser::exec_parse::parse_component_values;
use clazel_css::parser::rows::ExecRow;
use clazel_css::tokenizer::exec::{ExecToken, next_token};

use crate::values::items::{Span, number, push_str, top_level};
use crate::values::number::Num;

/// One component value, without the contents of a function or a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Tok {
    /// `<whitespace-token>`.
    Ws,
    /// `<ident-token>`.
    Ident(Span),
    /// `<number-token>`, and whether its type flag is "integer".
    Number {
        /// The value.
        value: Num,
        /// True for an integer.
        integer: bool,
    },
    /// `<dimension-token>`.
    Dimension {
        /// The value.
        value: Num,
        /// The unit.
        unit: Span,
    },
    /// `<delim-token>`.
    Delim(u32),
    /// `<colon-token>`.
    Colon,
    /// `<comma-token>`.
    Comma,
    /// A `( … )` simple block, and the index of the token after its contents.
    Paren {
        /// The index after the contents.
        end: u32,
    },
    /// A function, its name, and the index after its arguments.
    Function {
        /// The name.
        name: Span,
        /// The index after the arguments.
        end: u32,
    },
    /// A `[ … ]` or `{ … }` simple block, and the index after its contents.
    Block {
        /// The index after the contents.
        end: u32,
    },
    /// `<bad-string-token>`, `<bad-url-token>`, or an unmatched `)`, `]` or `}`: what
    /// `<any-value>` excludes (CSS Values 4 §2.6†), so `<general-enclosed>` cannot hold one.
    Bad,
    /// Any other token: `<string-token>`, `<url-token>`, `<hash-token>`,
    /// `<percentage-token>`, `<at-keyword-token>`, `<semicolon-token>`, `<CDO-token>`,
    /// `<CDC-token>`.
    Other,
}

/// The tokens of one list, and the text their spans are in.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Toks {
    /// The strings of the tokens.
    pub text: Vec<u32>,
    /// The tokens, in pre-order.
    pub toks: Vec<Tok>,
}

impl Toks {
    /// "Parse a list of component values" (CSS Syntax 3 §5.4.9) of `input`, flattened; empty
    /// if the input is longer than `clazel-css` accepts (which no attribute value reaching
    /// here is: the HTML tokenizer's input is bounded far below it).
    pub fn parse(input: &[u32]) -> Toks {
        if input.len() > MAX_PARSER_INPUT {
            return Toks::default();
        }
        let parsed = parse_component_values(input);
        let rows = parsed.output.rows.as_slice();
        Toks::from_row_range(parsed.text.as_slice(), rows, 0, rows.len())
    }

    /// The tokens of the list of rows `lo` up to `hi` of `rows` over `text`, as
    /// `clazel-css`'s exec parser leaves them (an at-rule's prelude is such a range). Read
    /// as [`crate::values::items::Values::from_row_range`] reads rows: rows that are not
    /// well formed read as an empty subtree or the end-of-file token, which is dropped.
    pub fn from_row_range(text: &[u32], rows: &[ExecRow], lo: usize, hi: usize) -> Toks {
        let mut out = Toks::default();
        // Each frame: the rows of a list still to read, last first, and the token whose end
        // it sets. As in `Values::from_row_range`, at most two steps per row and one more.
        let mut stack: Vec<(Vec<usize>, Option<usize>)> =
            vec![(top_level(rows, lo, hi.min(rows.len())), None)];
        for _ in 0..rows.len().saturating_mul(2).saturating_add(1) {
            let Some(frame) = stack.last_mut() else {
                break;
            };
            let Some(r) = frame.0.pop() else {
                let owner = frame.1;
                stack.pop();
                if let Some(i) = owner {
                    let end = u32::try_from(out.toks.len()).unwrap_or(u32::MAX);
                    if let Some(
                        Tok::Paren { end: e }
                        | Tok::Function { end: e, .. }
                        | Tok::Block { end: e },
                    ) = out.toks.get_mut(i)
                    {
                        *e = end;
                    }
                }
                continue;
            };
            let Some(row) = rows.get(r) else { continue };
            let pos = row.pos as usize;
            let token = if pos <= text.len() {
                next_token(text, pos, false).0
            } else {
                ExecToken::Eof
            };
            let here = out.toks.len();
            let tok = match &token {
                ExecToken::Whitespace => Tok::Ws,
                ExecToken::Ident { value } => Tok::Ident(push_str(&mut out.text, value)),
                ExecToken::Function { value } => Tok::Function {
                    name: push_str(&mut out.text, value),
                    end: 0,
                },
                ExecToken::OpenParen => Tok::Paren { end: 0 },
                ExecToken::OpenSquare | ExecToken::OpenCurly => Tok::Block { end: 0 },
                ExecToken::Number { number: n } => Tok::Number {
                    value: number(n),
                    integer: n.is_integer,
                },
                ExecToken::Dimension { number: n, unit } => Tok::Dimension {
                    value: number(n),
                    unit: push_str(&mut out.text, unit),
                },
                ExecToken::Delim { value } => Tok::Delim(*value),
                ExecToken::Colon => Tok::Colon,
                ExecToken::Comma => Tok::Comma,
                ExecToken::BadString
                | ExecToken::BadUrl
                | ExecToken::CloseParen
                | ExecToken::CloseSquare
                | ExecToken::CloseCurly => Tok::Bad,
                ExecToken::Eof => continue,
                _ => Tok::Other,
            };
            out.toks.push(tok);
            if matches!(
                tok,
                Tok::Paren { .. } | Tok::Function { .. } | Tok::Block { .. }
            ) {
                let start = row.start as usize;
                let children = if start <= r {
                    top_level(rows, start, r)
                } else {
                    Vec::new()
                };
                stack.push((children, Some(here)));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        Toks::parse(&input).toks
    }

    #[test]
    fn keeps_whitespace_colons_and_brackets() {
        let t = toks("a (b: 1px) [x] f(<=)");
        assert_eq!(
            t,
            vec![
                Tok::Ident(Span { start: 0, len: 1 }),
                Tok::Ws,
                Tok::Paren { end: 7 },
                Tok::Ident(Span { start: 1, len: 1 }),
                Tok::Colon,
                Tok::Ws,
                Tok::Dimension {
                    value: Num::from_int(1),
                    unit: Span { start: 2, len: 2 }
                },
                Tok::Ws,
                Tok::Block { end: 10 },
                Tok::Ident(Span { start: 4, len: 1 }),
                Tok::Ws,
                Tok::Function {
                    name: Span { start: 5, len: 1 },
                    end: 14
                },
                Tok::Delim(0x3C),
                Tok::Delim(0x3D),
            ]
        );
    }

    #[test]
    fn unmatched_closers_and_bad_strings_are_bad() {
        assert_eq!(
            toks("a)"),
            vec![Tok::Ident(Span { start: 0, len: 1 }), Tok::Bad]
        );
        assert_eq!(toks("\"x\n"), vec![Tok::Bad, Tok::Ws]);
    }
}
