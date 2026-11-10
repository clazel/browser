//! The component values a value grammar reads, flattened.
//!
//! `clazel-css` parses a declaration's value into component values (CSS Syntax 3 §5.4,
//! "parse a list of component values"), as rows in post-order. The grammars here read them
//! left to right, so [`Values::parse`] turns the rows into [`Item`]s in pre-order: a
//! function or a simple block is one item followed by its contents, and its `end` is the
//! index of the item after them. Whitespace is dropped, since no grammar of the subset
//! gives it a meaning (CSS Values 4 §2.2: components are separated by optional whitespace
//! unless the grammar says otherwise, and none here does). The strings of tokens go into
//! one text, and an item holds a [`Span`] of it, so an item is a few words and owns no
//! memory.
//!
//! Nothing assumes the items are well formed: a reader clamps every `end` to the list it
//! is in and every span to the text, so the Kani harnesses can run the grammars on any
//! items at all.

use clazel_css::parser::contract::MAX_PARSER_INPUT;
use clazel_css::parser::exec_parse::parse_component_values;
use clazel_css::parser::rows::ExecRow;
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, next_token};

use super::number::Num;

/// Code points `start .. start + len` of the text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Span {
    /// The first.
    pub start: u32,
    /// How many.
    pub len: u32,
}

/// One component value, without the contents of a function or a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Item {
    /// `<ident-token>`.
    Ident(Span),
    /// A function: its name, and the index after its arguments.
    Function {
        /// The name.
        name: Span,
        /// The index of the item after the arguments.
        end: u32,
    },
    /// `<hash-token>`.
    Hash(Span),
    /// `<string-token>`.
    String(Span),
    /// `<url-token>`.
    Url(Span),
    /// `<delim-token>`.
    Delim(u32),
    /// `<number-token>`, with the digits of its number part (for the hashless colour
    /// quirk) and whether it had a sign character.
    Number {
        /// The value.
        value: Num,
        /// The number part as written: sign, digits and any `.` and digits.
        repr: Span,
        /// True if the number part starts with `+` or `-`.
        signed: bool,
    },
    /// `<percentage-token>`.
    Percentage(Num),
    /// `<dimension-token>`.
    Dimension {
        /// The value.
        value: Num,
        /// The unit.
        unit: Span,
        /// The number part as written.
        repr: Span,
        /// True if the number part starts with `+` or `-`.
        signed: bool,
    },
    /// `<comma-token>`.
    Comma,
    /// A simple block, and the index of the item after its contents.
    Block {
        /// The index of the item after the contents.
        end: u32,
    },
    /// Any other token: no grammar of the subset accepts one.
    Other,
}

/// The items of one value, and the text their spans are in.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Values {
    /// The strings of the tokens.
    pub text: Vec<u32>,
    /// The items, in pre-order.
    pub items: Vec<Item>,
}

/// Borrowed [`Values`].
#[derive(Debug, Clone, Copy)]
pub struct Src<'a> {
    /// The strings.
    pub text: &'a [u32],
    /// The items.
    pub items: &'a [Item],
}

impl<'a> Src<'a> {
    /// The code points of `s`, or none if it is outside the text.
    pub fn str(&self, s: Span) -> &'a [u32] {
        let start = s.start as usize;
        let end = start.saturating_add(s.len as usize);
        self.text.get(start..end).unwrap_or_default()
    }
}

/// A position in a list of items: `pos` up to `end`.
#[derive(Debug, Clone, Copy)]
pub struct Cursor<'a> {
    /// What is read.
    pub src: Src<'a>,
    /// The next item.
    pub pos: usize,
    /// The end of the list.
    pub end: usize,
}

/// ASCII lower case of one code point.
pub fn lower(c: u32) -> u32 {
    if (0x41..=0x5A).contains(&c) {
        c.saturating_add(0x20)
    } else {
        c
    }
}

/// True if `s` is `target` (written in lower case), ASCII case-insensitively.
pub fn eq_ignore_case(s: &[u32], target: &str) -> bool {
    s.len() == target.len()
        && s.iter()
            .zip(target.bytes())
            .all(|(&c, b)| lower(c) == u32::from(b))
}

/// The entry of `table` whose name is `s`, ASCII case-insensitively.
pub fn lookup<T: Copy>(table: &[(&'static str, T)], s: &[u32]) -> Option<T> {
    table
        .iter()
        .find(|(name, _)| eq_ignore_case(s, name))
        .map(|(_, v)| *v)
}

/// The keyword of `table` that `s` is, ASCII case-insensitively.
pub fn keyword_in(table: &[&'static str], s: &[u32]) -> Option<&'static str> {
    table.iter().copied().find(|k| eq_ignore_case(s, k))
}

impl<'a> Cursor<'a> {
    /// The whole of `src`.
    pub fn new(src: Src<'a>) -> Cursor<'a> {
        Cursor {
            src,
            pos: 0,
            end: src.items.len(),
        }
    }

    /// True if nothing is left.
    pub fn at_end(&self) -> bool {
        self.pos >= self.end
    }

    /// The next item, not consumed.
    pub fn peek(&self) -> Option<Item> {
        if self.at_end() {
            None
        } else {
            self.src.items.get(self.pos).copied()
        }
    }

    /// Where the item at `pos` ends: past its contents if it has any, clamped to this list.
    fn item_end(&self, item: Item) -> usize {
        let next = self.pos.saturating_add(1);
        match item {
            Item::Function { end, .. } | Item::Block { end } => {
                (end as usize).clamp(next, self.end.max(next))
            }
            _ => next,
        }
    }

    /// Consume the next item, and any contents.
    pub fn bump(&mut self) -> Option<Item> {
        let item = self.peek()?;
        self.pos = self.item_end(item);
        Some(item)
    }

    /// If the next item is a function, consume it and return its name and a cursor over
    /// its arguments.
    pub fn function(&mut self) -> Option<(&'a [u32], Cursor<'a>)> {
        let item = self.peek()?;
        let Item::Function { name, .. } = item else {
            return None;
        };
        let start = self.pos.saturating_add(1);
        let end = self.item_end(item);
        self.pos = end;
        Some((
            self.src.str(name),
            Cursor {
                src: self.src,
                pos: start,
                end,
            },
        ))
    }

    /// If the next item is an ident, consume it and return its value.
    pub fn ident(&mut self) -> Option<&'a [u32]> {
        if let Some(Item::Ident(s)) = self.peek() {
            self.pos = self.pos.saturating_add(1);
            Some(self.src.str(s))
        } else {
            None
        }
    }

    /// If the next item is an ident in `table`, consume it and return the keyword.
    pub fn keyword(&mut self, table: &[&'static str]) -> Option<&'static str> {
        let save = self.pos;
        let k = self.ident().and_then(|s| keyword_in(table, s));
        if k.is_none() {
            self.pos = save;
        }
        k
    }

    /// If the next item is the ident `k` (in lower case), consume it.
    pub fn eat_keyword(&mut self, k: &'static str) -> bool {
        self.keyword(&[k]).is_some()
    }

    /// If the next item is a comma, consume it.
    pub fn comma(&mut self) -> bool {
        if self.peek() == Some(Item::Comma) {
            self.pos = self.pos.saturating_add(1);
            true
        } else {
            false
        }
    }

    /// If the next item is the delim `c`, consume it.
    pub fn delim(&mut self, c: u32) -> bool {
        if self.peek() == Some(Item::Delim(c)) {
            self.pos = self.pos.saturating_add(1);
            true
        } else {
            false
        }
    }
}

/// The text of an [`ExecNumber`]'s number part, pushed onto `text`.
fn push_str(text: &mut Vec<u32>, s: &[u32]) -> Span {
    let start = u32::try_from(text.len()).unwrap_or(u32::MAX);
    text.extend_from_slice(s);
    Span {
        start,
        len: u32::try_from(s.len()).unwrap_or(0),
    }
}

fn number(n: &ExecNumber) -> Num {
    Num::from_parts(&n.number_part, &n.exponent_part, n.is_integer)
}

fn signed(n: &ExecNumber) -> bool {
    n.sign_character.is_some()
}

/// The rows of `rows` that make the list `lo .. hi`, first to last: the last value of the
/// list is row `hi - 1`, and the one before it ends where that one's subtree starts.
fn top_level(rows: &[ExecRow], lo: usize, hi: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut k = hi;
    while k > lo {
        let r = k.saturating_sub(1);
        out.push(r);
        let start = rows.get(r).map_or(lo, |row| row.start as usize);
        // A subtree starts at or before its own row; anything else is not a list.
        k = if start <= r && start >= lo { start } else { lo };
    }
    out.reverse();
    out
}

impl Values {
    /// "Parse a list of component values" (CSS Syntax 3 §5.4.9) of `input`, flattened.
    /// `None` if the input is longer than `clazel-css` accepts.
    pub fn parse(input: &[u32]) -> Option<Values> {
        if input.len() > MAX_PARSER_INPUT {
            return None;
        }
        let parsed = parse_component_values(input);
        let text = parsed.text.as_slice();
        let rows = parsed.output.rows.as_slice();
        let mut out = Values::default();
        // Each frame: the rows of a list, the next one, and the item whose end it sets.
        let mut stack: Vec<(Vec<usize>, usize, Option<usize>)> =
            vec![(top_level(rows, 0, rows.len()), 0, None)];
        while let Some(frame) = stack.last_mut() {
            let Some(&r) = frame.0.get(frame.1) else {
                let owner = frame.2;
                stack.pop();
                if let Some(i) = owner {
                    let end = u32::try_from(out.items.len()).unwrap_or(u32::MAX);
                    if let Some(Item::Function { end: e, .. } | Item::Block { end: e }) =
                        out.items.get_mut(i)
                    {
                        *e = end;
                    }
                }
                continue;
            };
            frame.1 = frame.1.saturating_add(1);
            let Some(row) = rows.get(r) else { continue };
            let pos = row.pos as usize;
            let token = if pos <= text.len() {
                next_token(text, pos, false).0
            } else {
                ExecToken::Eof
            };
            let here = out.items.len();
            let item = match &token {
                ExecToken::Ident { value } => Item::Ident(push_str(&mut out.text, value)),
                ExecToken::Function { value } => Item::Function {
                    name: push_str(&mut out.text, value),
                    end: 0,
                },
                ExecToken::OpenParen | ExecToken::OpenSquare | ExecToken::OpenCurly => {
                    Item::Block { end: 0 }
                }
                ExecToken::Hash { value, .. } => Item::Hash(push_str(&mut out.text, value)),
                ExecToken::String { value } => Item::String(push_str(&mut out.text, value)),
                ExecToken::Url { value } => Item::Url(push_str(&mut out.text, value)),
                ExecToken::Delim { value } => Item::Delim(*value),
                ExecToken::Number { number: n } => Item::Number {
                    value: number(n),
                    repr: push_str(&mut out.text, &n.number_part),
                    signed: signed(n),
                },
                ExecToken::Percentage { number: n } => Item::Percentage(number(n)),
                ExecToken::Dimension { number: n, unit } => {
                    let unit = push_str(&mut out.text, unit);
                    Item::Dimension {
                        value: number(n),
                        unit,
                        repr: push_str(&mut out.text, &n.number_part),
                        signed: signed(n),
                    }
                }
                ExecToken::Comma => Item::Comma,
                ExecToken::Whitespace => continue,
                _ => Item::Other,
            };
            out.items.push(item);
            if matches!(item, Item::Function { .. } | Item::Block { .. }) {
                let start = row.start as usize;
                let children = if start <= r {
                    top_level(rows, start, r)
                } else {
                    Vec::new()
                };
                stack.push((children, 0, Some(here)));
            }
        }
        Some(out)
    }

    /// The items, borrowed.
    pub fn src(&self) -> Src<'_> {
        Src {
            text: &self.text,
            items: &self.items,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn values(s: &str) -> Values {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        Values::parse(&input).unwrap_or_default()
    }

    #[test]
    fn flattens_in_pre_order() -> Result<(), String> {
        let v = values("a rgb(1, 2) [x] , 3px");
        let kinds: Vec<&str> = v
            .items
            .iter()
            .map(|i| match i {
                Item::Ident(_) => "ident",
                Item::Function { .. } => "function",
                Item::Number { .. } => "number",
                Item::Comma => "comma",
                Item::Block { .. } => "block",
                Item::Dimension { .. } => "dimension",
                _ => "other",
            })
            .collect();
        assert_eq!(
            kinds,
            [
                "ident",
                "function",
                "number",
                "comma",
                "number",
                "block",
                "ident",
                "comma",
                "dimension"
            ]
        );
        assert_eq!(
            v.items.get(1),
            Some(&Item::Function {
                name: Span { start: 1, len: 3 },
                end: 5
            })
        );
        assert_eq!(v.items.get(5), Some(&Item::Block { end: 7 }));
        let mut c = Cursor::new(v.src());
        assert!(c.ident().is_some());
        let (name, mut args) = c.function().ok_or("no function")?;
        assert!(eq_ignore_case(name, "rgb"));
        assert!(matches!(args.bump(), Some(Item::Number { .. })));
        assert!(args.comma());
        assert!(args.bump().is_some() && args.at_end());
        assert!(matches!(c.bump(), Some(Item::Block { .. })));
        assert!(c.comma());
        Ok(())
    }

    #[test]
    fn nested_functions_end_after_their_contents() {
        let v = values("f(g(1) 2) 3");
        assert_eq!(
            v.items.first(),
            Some(&Item::Function {
                name: Span { start: 0, len: 1 },
                end: 4
            })
        );
        assert_eq!(
            v.items.get(1),
            Some(&Item::Function {
                name: Span { start: 1, len: 1 },
                end: 3
            })
        );
        assert_eq!(v.items.len(), 5);
    }

    #[test]
    fn comments_and_whitespace_are_dropped() {
        assert_eq!(values(" /* x */ a /**/ ").items.len(), 1);
        assert!(values("").items.is_empty());
    }
}
