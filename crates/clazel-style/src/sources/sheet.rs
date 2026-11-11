//! A style sheet's rules, as the cascade reads them: its style rules in order, each with the
//! `@media` rule it is inside, and the declarations of a `style` attribute.
//!
//! `clazel-css` parses a sheet ("parse a stylesheet", CSS Syntax 3 §5.4.3) into flat arrays
//! in post-order (`clazel_css::parser::rows`). This walks them once, iteratively, in the
//! sheet's order:
//!
//! - a qualified rule at the top level or directly inside `@media` is a style rule: its
//!   prelude's text (the selector list, which `clazel-selectors` parses) and its
//!   declarations;
//! - `@media` (CSS Conditional 3 §6.1†, its prelude a `<media-query-list>`, Media Queries 4
//!   §3) becomes a [`MediaBlock`], and the rules inside it point at it; `@media` inside
//!   `@media` points at its parent, so a rule applies when every enclosing list matches;
//! - `@import`, `@supports`, `@font-face`, `@namespace` and `@page` are recognised and
//!   ignored (phase-5.md item 5.8), with whatever they contain, and listed in
//!   [`StyleSheet::ignored`]; any other at-rule, `@charset` included (CSS Syntax 3 §8.3:
//!   "treated as an unrecognized rule"), is dropped as CSS Syntax says an unknown rule is.
//!
//! Not read, and listed in the README: rules nested inside a style rule (CSS Nesting) and
//! declarations directly inside `@media`, neither of which the subset has.

use clazel_css::input::exec::decode_stylesheet;
use clazel_css::parser::contract::MAX_PARSER_INPUT;
use clazel_css::parser::exec_parse::{
    ExecParsed, parse_declaration_list, parse_stylesheet_contents,
};
use clazel_css::parser::rows::{
    ExecDeclaration, ExecDeclarationKind, ExecItem, ExecItemKind, ExecRow,
};
use clazel_css::tokenizer::exec::{ExecToken, next_token};
use clazel_encoding::labels::spec::Encoding;

use super::media::{Device, MediaQueryList, evaluate, parse_media_query_list};
use super::tokens::Toks;
use crate::values::items::{Values, eq_ignore_case};

/// One declaration: its name, its value as the items `values/` reads, and `!important`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    /// The property name, as written.
    pub name: Vec<u32>,
    /// The value, without `!important` (CSS Syntax 3 §5.5.5 takes it off).
    pub value: Values,
    /// The important flag.
    pub important: bool,
}

/// A style rule: a qualified rule whose prelude is a selector list (CSS Syntax 3 §9†).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StyleRule {
    /// The prelude's text, from its first component value to the end of its last.
    pub selectors: Vec<u32>,
    /// Its declarations, in order.
    pub declarations: Vec<Declaration>,
    /// The innermost `@media` rule it is inside, an index into [`StyleSheet::media`].
    pub media: Option<usize>,
}

/// An `@media` rule's condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MediaBlock {
    /// Its media query list.
    pub queries: MediaQueryList,
    /// The `@media` rule it is inside, an earlier index.
    pub parent: Option<usize>,
}

/// An at-rule that is recognised and ignored (phase-5.md item 5.8).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ignored {
    /// `@import`.
    Import,
    /// `@supports`.
    Supports,
    /// `@font-face`.
    FontFace,
    /// `@namespace`.
    Namespace,
    /// `@page`.
    Page,
}

/// The at-rules recognised and ignored, by name.
const IGNORED: &[(&str, Ignored)] = &[
    ("import", Ignored::Import),
    ("supports", Ignored::Supports),
    ("font-face", Ignored::FontFace),
    ("namespace", Ignored::Namespace),
    ("page", Ignored::Page),
];

/// A parsed style sheet.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StyleSheet {
    /// The style rules, in order.
    pub rules: Vec<StyleRule>,
    /// The `@media` rules, each after its parent.
    pub media: Vec<MediaBlock>,
    /// The ignored at-rules, in order.
    pub ignored: Vec<Ignored>,
}

/// The items `lo .. hi` of a list of `items`, first to last: the last is item `hi - 1`, and
/// the one before it ends where that one's block starts (`clazel_css::parser::rows`).
fn children(items: &[ExecItem], lo: usize, hi: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut k = hi.min(items.len());
    for _ in 0..items.len().saturating_add(1) {
        if k <= lo {
            break;
        }
        let i = k.saturating_sub(1);
        out.push(i);
        let start = items.get(i).map_or(lo, |it| it.start as usize);
        k = if start <= i && start >= lo { start } else { lo };
    }
    out.reverse();
    out
}

/// The token at `pos` of `text`, if `pos` is inside it.
fn token_at(text: &[u32], pos: u32) -> Option<(ExecToken, usize)> {
    let pos = pos as usize;
    (pos <= text.len()).then(|| next_token(text, pos, false))
}

/// Where the value whose row is `rows[k]` ends in `text`: after its token, or after the
/// token closing its block or function (or at the end of the text, if none does).
fn value_end(text: &[u32], rows: &[ExecRow], k: usize) -> usize {
    let Some(row) = rows.get(k) else { return 0 };
    let Some((first, mut pos)) = token_at(text, row.pos) else {
        return text.len();
    };
    // The closers still owed, innermost last: a block ends at the token matching its
    // opener (CSS Syntax 3 §5.5.8 "consume a simple block", §5.5.9 "consume a function").
    let closer = |t: &ExecToken| match t {
        ExecToken::Function { .. } | ExecToken::OpenParen => Some(ExecToken::CloseParen),
        ExecToken::OpenSquare => Some(ExecToken::CloseSquare),
        ExecToken::OpenCurly => Some(ExecToken::CloseCurly),
        _ => None,
    };
    let mut owed: Vec<ExecToken> = closer(&first).into_iter().collect();
    for _ in 0..text.len().saturating_add(1) {
        let Some(want) = owed.last() else { break };
        if pos >= text.len() {
            return text.len();
        }
        let (t, next) = next_token(text, pos, false);
        if next <= pos {
            return text.len();
        }
        pos = next;
        if &t == want {
            owed.pop();
        } else if let Some(c) = closer(&t) {
            owed.push(c);
        }
    }
    pos.min(text.len())
}

/// The text of the rows `lo .. hi` of `rows`: from the first token of the list to the end of
/// its last value.
fn list_text(text: &[u32], rows: &[ExecRow], lo: usize, hi: usize) -> Vec<u32> {
    let hi = hi.min(rows.len());
    let Some(start) = rows.get(lo..hi).and_then(|r| r.iter().map(|r| r.pos).min()) else {
        return Vec::new();
    };
    let end = value_end(text, rows, hi.saturating_sub(1));
    text.get(start as usize..end).unwrap_or_default().to_vec()
}

/// One declaration of a parse; `None` if its name is not an identifier, or for a
/// `unicode-range` declaration, whose value rows are read in another text and which is not
/// a property of the subset.
fn declaration(parsed: &ExecParsed, d: &ExecDeclaration) -> Option<Declaration> {
    if d.kind == ExecDeclarationKind::UnicodeRange {
        return None;
    }
    let ExecToken::Ident { value: name } = token_at(&parsed.text, d.name_pos)?.0 else {
        return None;
    };
    Some(Declaration {
        name,
        value: Values::from_row_range(
            &parsed.text,
            &parsed.output.rows,
            d.value_lo as usize,
            d.value_hi as usize,
        ),
        important: d.important,
    })
}

/// The declarations `lo .. hi` of a parse.
fn declarations_of(parsed: &ExecParsed, lo: u32, hi: u32) -> Vec<Declaration> {
    parsed
        .output
        .declarations
        .get(lo as usize..hi as usize)
        .unwrap_or_default()
        .iter()
        .filter_map(|d| declaration(parsed, d))
        .collect()
}

impl StyleSheet {
    /// "Parse a stylesheet" (CSS Syntax 3 §5.4.3, whose rules are "parse a stylesheet's contents" of the
    /// input, §5.4.2) of `input`, already decoded, and read its
    /// rules. Input longer than `clazel-css` accepts (2^29 code points, beyond any body the
    /// renderer is sent) is an empty sheet.
    pub fn parse(input: &[u32]) -> StyleSheet {
        if input.len() > MAX_PARSER_INPUT {
            return StyleSheet::default();
        }
        let parsed = parse_stylesheet_contents(input);
        StyleSheet::from_parsed(&parsed)
    }

    /// A fetched sheet's bytes decoded (CSS Syntax 3 §3.2 "decode", with the protocol's
    /// `charset` label and the environment encoding) and parsed. `None` if `clazel-encoding`
    /// has no decoder for the encoding the bytes need.
    pub fn from_bytes(
        bytes: &[u8],
        protocol_label: Option<&[u32]>,
        environment_encoding: Option<Encoding>,
    ) -> Option<StyleSheet> {
        let input = decode_stylesheet(bytes, protocol_label, environment_encoding)?;
        Some(StyleSheet::parse(&input))
    }

    /// The rules of a parse, in order.
    pub fn from_parsed(parsed: &ExecParsed) -> StyleSheet {
        let items = parsed.output.items.as_slice();
        let rows = parsed.output.rows.as_slice();
        let text = parsed.text.as_slice();
        let mut sheet = StyleSheet::default();
        // Each frame: the items of a list still to read, last first, and the `@media` rule
        // they are inside. Every item is in at most one frame, so there are at most two
        // steps per item and one for the last frame.
        let mut top = children(items, 0, items.len());
        top.reverse();
        let mut stack: Vec<(Vec<usize>, Option<usize>)> = vec![(top, None)];
        for _ in 0..items.len().saturating_mul(2).saturating_add(1) {
            let Some(frame) = stack.last_mut() else { break };
            let media = frame.1;
            let Some(k) = frame.0.pop() else {
                stack.pop();
                continue;
            };
            let Some(item) = items.get(k) else { continue };
            match item.kind {
                ExecItemKind::QualifiedRule => {
                    // CSS Syntax 3 §5.5.3: "If the first item of child rules is a list of
                    // declarations, remove it from child rules and assign it to rule's
                    // declarations." The other child rules (nesting) are not read.
                    let declarations = children(items, item.start as usize, k)
                        .first()
                        .and_then(|&c| items.get(c))
                        .filter(|c| c.kind == ExecItemKind::Declarations)
                        .map(|c| declarations_of(parsed, c.lo, c.hi))
                        .unwrap_or_default();
                    sheet.rules.push(StyleRule {
                        selectors: list_text(text, rows, item.lo as usize, item.hi as usize),
                        declarations,
                        media,
                    });
                }
                ExecItemKind::BlockAtRule | ExecItemKind::StatementAtRule => {
                    let Some((ExecToken::AtKeyword { value: name }, _)) = token_at(text, item.pos)
                    else {
                        continue;
                    };
                    if eq_ignore_case(&name, "media") && item.kind == ExecItemKind::BlockAtRule {
                        let toks =
                            Toks::from_row_range(text, rows, item.lo as usize, item.hi as usize);
                        let index = sheet.media.len();
                        sheet.media.push(MediaBlock {
                            queries: parse_media_query_list(&toks),
                            parent: media,
                        });
                        let mut inner = children(items, item.start as usize, k);
                        inner.reverse();
                        stack.push((inner, Some(index)));
                    } else if let Some(&(_, ignored)) =
                        IGNORED.iter().find(|(n, _)| eq_ignore_case(&name, n))
                    {
                        sheet.ignored.push(ignored);
                    }
                }
                // Declarations directly inside `@media`: not in the subset.
                ExecItemKind::Declarations => {}
            }
        }
        sheet
    }

    /// Which `@media` rules apply on `device`: each one's list matches and so does its
    /// parent's. One pass, since a parent comes before its children.
    pub fn active_media(&self, device: Device) -> Vec<bool> {
        let mut active: Vec<bool> = Vec::with_capacity(self.media.len());
        for (i, m) in self.media.iter().enumerate() {
            let parent = m
                .parent
                .is_none_or(|p| p < i && active.get(p).copied().unwrap_or(false));
            active.push(parent && evaluate(&m.queries, device));
        }
        active
    }

    /// The style rules that apply on `device`, in order: those outside `@media`, and those
    /// inside `@media` rules that all match.
    pub fn rules_for(&self, device: Device) -> Vec<&StyleRule> {
        let active = self.active_media(device);
        self.rules
            .iter()
            .filter(|r| {
                r.media
                    .is_none_or(|m| active.get(m).copied().unwrap_or(false))
            })
            .collect()
    }
}

/// A `style` attribute's declarations: CSS Style Attributes §3, "the same forward-compatible
/// parsing rules that apply to parsing declaration block contents", which CSSOM §6.7† "parse
/// a CSS declaration block" gives as CSS Syntax 3's "parse a list of declarations"
/// (§5.4.5). Which of them are valid is the property grammars' to say (`values/`).
pub fn style_attribute(value: &[u32]) -> Vec<Declaration> {
    if value.len() > MAX_PARSER_INPUT {
        return Vec::new();
    }
    let parsed = parse_declaration_list(value);
    let n = u32::try_from(parsed.output.declarations.len()).unwrap_or(u32::MAX);
    declarations_of(&parsed, 0, n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::{get_property_value, parse_items, property};

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    /// `name: value` read by `values/`, as the cascade will.
    fn read(d: &Declaration) -> String {
        let Some(p) = property(&d.name) else {
            return String::new();
        };
        let block = parse_items(p, d.value.src(), false).unwrap_or_default();
        get_property_value(&block, &d.name)
    }

    #[test]
    fn style_rules_in_order() {
        let sheet = StyleSheet::parse(&u("@charset \"utf-8\";\n\
             body, td { font-family: Verdana, Geneva, sans-serif; font-size: 10pt !important }\n\
             a:link { color: #000000 }\n\
             .c00, .c00 a:link { color: rgb(0, 0, 0) ; }\n"));
        let sel: Vec<String> = sheet.rules.iter().map(|r| s(&r.selectors)).collect();
        assert_eq!(sel, ["body, td ", "a:link ", ".c00, .c00 a:link "]);
        let first = sheet
            .rules
            .first()
            .map(|r| r.declarations.clone())
            .unwrap_or_default();
        let read_all: Vec<(String, String, bool)> = first
            .iter()
            .map(|d| (s(&d.name), read(d), d.important))
            .collect();
        assert_eq!(
            read_all,
            [
                (
                    "font-family".to_owned(),
                    "Verdana, Geneva, sans-serif".to_owned(),
                    false
                ),
                ("font-size".to_owned(), "10pt".to_owned(), true),
            ]
        );
        assert!(sheet.media.is_empty() && sheet.ignored.is_empty());
    }

    #[test]
    fn selector_text_ends_after_its_last_block() {
        let sheet = StyleSheet::parse(&u("input[type='submit']{x:y} :is(a, (b)) {}"));
        let sel: Vec<String> = sheet.rules.iter().map(|r| s(&r.selectors)).collect();
        assert_eq!(sel, ["input[type='submit']", ":is(a, (b)) "]);
    }

    #[test]
    fn media_rules_nest_and_gate() {
        let sheet = StyleSheet::parse(&u("a{}\n\
             @media only screen and (min-width: 300px) and (max-width: 750px) { b{} \
               @MEDIA (orientation: landscape) { c{} } d{} }\n\
             @media print { e{} }\n\
             @media (-webkit-min-device-pixel-ratio: 2), (min-device-pixel-ratio: 2) { f{} }\n\
             g{}"));
        assert_eq!(sheet.media.len(), 4);
        assert_eq!(sheet.media.get(1).and_then(|m| m.parent), Some(0));
        let names = |w, h| -> Vec<String> {
            sheet
                .rules_for(Device::screen(w, h))
                .iter()
                .map(|r| s(&r.selectors).trim().to_owned())
                .collect()
        };
        assert_eq!(names(500, 400), ["a", "b", "c", "d", "g"]);
        assert_eq!(names(500, 600), ["a", "b", "d", "g"]);
        assert_eq!(names(800, 400), ["a", "g"]);
    }

    #[test]
    fn ignored_and_unknown_at_rules() {
        let sheet = StyleSheet::parse(&u("@import url(a.css) screen; @namespace svg url(x);\n\
             @supports (display: grid) { a{} }\n\
             @font-face { font-family: x; src: url(x.ttf) }\n\
             @page :first { margin: 1in }\n\
             @keyframes k { from {} }\n\
             @media { declared: here; b{} }\n\
             @media screen;\n\
             c{}"));
        assert_eq!(
            sheet.ignored,
            [
                Ignored::Import,
                Ignored::Namespace,
                Ignored::Supports,
                Ignored::FontFace,
                Ignored::Page
            ]
        );
        let sel: Vec<String> = sheet
            .rules
            .iter()
            .map(|r| s(&r.selectors).trim().to_owned())
            .collect();
        assert_eq!(sel, ["b", "c"]);
        assert_eq!(sheet.rules_for(Device::screen(1, 1)).len(), 2);
    }

    #[test]
    fn style_attributes() {
        let d = style_attribute(&u("margin-top:2px; margin-bottom:-10px;"));
        let got: Vec<(String, String)> = d.iter().map(|d| (s(&d.name), read(d))).collect();
        assert_eq!(
            got,
            [
                ("margin-top".to_owned(), "2px".to_owned()),
                ("margin-bottom".to_owned(), "-10px".to_owned()),
            ]
        );
        // CSS Style Attributes §3: a `}` is "merely an invalid token", and an at-rule does
        // not swallow the declaration after it.
        let d = style_attribute(&u(
            "color: red } ; @unsupported { splines: reticulating } color: green",
        ));
        let got: Vec<String> = d
            .iter()
            .map(|d| format!("{}={}", s(&d.name), read(d)))
            .collect();
        assert_eq!(got.last().map(String::as_str), Some("color=green"));
        assert!(style_attribute(&u("")).is_empty());
    }

    #[test]
    fn decoding_a_fetched_sheet() -> Result<(), String> {
        // Latin-1 bytes, labelled by the protocol.
        let label = u("iso-8859-1");
        let sheet = StyleSheet::from_bytes(b"a{content:\"\xe9\"}", Some(&label), None)
            .ok_or("no decoder")?;
        assert_eq!(sheet.rules.len(), 1);
        let sheet = StyleSheet::from_bytes(
            b"@charset \"utf-8\"; b{}",
            None,
            Some(Encoding::Windows1252),
        )
        .ok_or("no decoder")?;
        assert_eq!(sheet.rules.len(), 1);
        Ok(())
    }
}
