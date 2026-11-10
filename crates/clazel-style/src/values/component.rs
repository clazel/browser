//! A specified value as a list of components, and CSSOM's serialization of one.
//!
//! Every longhand's value is a list of [`Component`]s in the order CSSOM serializes them
//! (the grammar's canonical order, where it reorders), so one serializer serves all of
//! them: components are separated by a space, a [`Component::Comma`] by ", " and a
//! [`Component::Slash`] by " / ". CSSOM, "serialize a CSS value"†, at
//! <https://drafts.csswg.org/cssom-1/#serialize-a-css-value>.

use super::color::{Color, write_color};
use super::number::{Angle, Length, Num, write_num};

/// One component of a specified value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Component {
    /// A keyword, in lower case.
    Keyword(&'static str),
    /// A `<custom-ident>`, as written.
    Ident(Vec<u32>),
    /// A `<length>`.
    Length(Length),
    /// A `<percentage>`.
    Percentage(Num),
    /// A `<number>` or `<integer>`.
    Number(Num),
    /// An `<angle>`.
    Angle(Angle),
    /// A `<color>`.
    Color(Color),
    /// A `<string>`.
    String(Vec<u32>),
    /// A `<url>`.
    Url(Vec<u32>),
    /// A font family name (CSS Fonts 4 `<family-name>`), its identifiers joined by single
    /// spaces if it was written unquoted.
    FamilyName(Vec<u32>),
    /// The start of a function, with its name: its arguments follow, up to the matching
    /// [`Component::Close`]. The list is flat rather than nested so that a value owns no
    /// recursive structure (whose drop the Kani harnesses would have to unwind).
    Open(&'static str),
    /// The end of a function.
    Close,
    /// A comma between list items.
    Comma,
    /// A `/` between two parts of a shorthand.
    Slash,
}

/// CSSOM "serialize a string": in double quotes, with `"` and `\` escaped, U+0000 as
/// U+FFFD and control characters as code point escapes.
pub fn write_string(out: &mut String, s: &[u32]) {
    out.push('"');
    for &c in s {
        match c {
            0 => out.push('\u{FFFD}'),
            0x01..=0x1F | 0x7F => out.push_str(&format!("\\{c:x} ")),
            0x22 => out.push_str("\\\""),
            0x5C => out.push_str("\\\\"),
            _ => out.push(char::from_u32(c).unwrap_or('\u{FFFD}')),
        }
    }
    out.push('"');
}

/// True if `c` may start an identifier without an escape (CSS Syntax 3 §4.2 "ident-start
/// code point").
fn ident_start(c: u32) -> bool {
    c == 0x5F || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) || c >= 0x80
}

/// True if `c` may continue an identifier without an escape ("ident code point").
fn ident_char(c: u32) -> bool {
    ident_start(c) || c == 0x2D || (0x30..=0x39).contains(&c)
}

/// True if `word` serializes as an identifier with no escape.
fn plain_ident(word: &[u32]) -> bool {
    match word {
        [] => false,
        [0x2D] => false,
        [0x2D, 0x2D, ..] => word.iter().all(|&c| ident_char(c)),
        [0x2D, second, ..] => ident_start(*second) && word.iter().all(|&c| ident_char(c)),
        [first, ..] => ident_start(*first) && word.iter().all(|&c| ident_char(c)),
    }
}

/// Names a family may not be written as unquoted: the generic families and the keywords a
/// `<custom-ident>` excludes (CSS Fonts 4 §2.1†, CSS Values 4 §4.2).
const RESERVED_FAMILY_WORDS: &[&str] = &[
    "serif",
    "sans-serif",
    "cursive",
    "fantasy",
    "monospace",
    "system-ui",
    "emoji",
    "math",
    "fangsong",
    "ui-serif",
    "ui-sans-serif",
    "ui-monospace",
    "ui-rounded",
    "initial",
    "inherit",
    "unset",
    "revert",
    "revert-layer",
    "default",
];

/// A font family name, unquoted if each of its space-separated words is an identifier and
/// the first is not reserved, else as a string. CSSOM leaves this to engines; this is what
/// the WPT cases expect of all of them.
fn write_family(out: &mut String, name: &[u32]) {
    let words: Vec<&[u32]> = name.split(|&c| c == 0x20).collect();
    let reserved = words.first().is_some_and(|w| {
        RESERVED_FAMILY_WORDS
            .iter()
            .any(|r| super::items::eq_ignore_case(w, r))
    });
    if !reserved && words.iter().all(|w| plain_ident(w)) {
        for &c in name {
            out.push(char::from_u32(c).unwrap_or('\u{FFFD}'));
        }
    } else {
        write_string(out, name);
    }
}

/// CSSOM "serialize an identifier", for a `<custom-ident>`.
fn write_ident(out: &mut String, s: &[u32]) {
    for (i, &c) in s.iter().enumerate() {
        let first = i == 0;
        let second_after_dash = i == 1 && s.first() == Some(&0x2D);
        if c == 0 {
            out.push('\u{FFFD}');
        } else if (0x01..=0x1F).contains(&c)
            || c == 0x7F
            || ((first || second_after_dash) && (0x30..=0x39).contains(&c))
        {
            out.push_str(&format!("\\{c:x} "));
        } else if first && c == 0x2D && s.len() == 1 {
            out.push_str("\\-");
        } else if ident_char(c) {
            out.push(char::from_u32(c).unwrap_or('\u{FFFD}'));
        } else {
            out.push('\\');
            out.push(char::from_u32(c).unwrap_or('\u{FFFD}'));
        }
    }
}

/// Append one component.
pub fn write_component(out: &mut String, c: &Component) {
    match c {
        Component::Keyword(k) => out.push_str(k),
        Component::Ident(s) => write_ident(out, s),
        Component::Length(l) => {
            write_num(out, l.value);
            out.push_str(l.unit.name());
        }
        Component::Percentage(p) => {
            write_num(out, *p);
            out.push('%');
        }
        Component::Number(n) => write_num(out, *n),
        Component::Angle(a) => {
            write_num(out, a.value);
            out.push_str(a.unit.name());
        }
        Component::Color(c) => write_color(out, *c),
        Component::String(s) => write_string(out, s),
        Component::Url(s) => {
            out.push_str("url(");
            write_string(out, s);
            out.push(')');
        }
        Component::FamilyName(s) => write_family(out, s),
        Component::Open(name) => {
            out.push_str(name);
            out.push('(');
        }
        Component::Close => out.push(')'),
        Component::Comma => out.push(','),
        Component::Slash => out.push('/'),
    }
}

/// Append a list of components, separated as the module says.
pub fn write_components(out: &mut String, list: &[Component]) {
    // True where no space goes before the next component: at the start, after a
    // separator and after a function's opening parenthesis.
    let mut tight = true;
    for c in list {
        match c {
            Component::Comma => out.push_str(", "),
            Component::Slash => out.push_str(" / "),
            Component::Close => out.push(')'),
            _ => {
                if !tight {
                    out.push(' ');
                }
                write_component(out, c);
            }
        }
        tight = matches!(c, Component::Comma | Component::Slash | Component::Open(_));
    }
}

/// True if `list` has a comma outside any function: a list of several items.
pub fn has_top_level_comma(list: &[Component]) -> bool {
    let mut depth = 0usize;
    for c in list {
        match c {
            Component::Open(_) => depth = depth.saturating_add(1),
            Component::Close => depth = depth.saturating_sub(1),
            Component::Comma if depth == 0 => return true,
            _ => {}
        }
    }
    false
}

/// A list of components, serialized.
pub fn to_string(list: &[Component]) -> String {
    let mut out = String::new();
    write_components(&mut out, list);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    #[test]
    fn families() {
        let f = |s: &str| to_string(&[Component::FamilyName(u(s))]);
        assert_eq!(f("New Century Schoolbook"), "New Century Schoolbook");
        assert_eq!(f("21st Century"), "\"21st Century\"");
        assert_eq!(f("inherit"), "\"inherit\"");
        assert_eq!(f("Serif"), "\"Serif\"");
        assert_eq!(f("a\"b"), "\"a\\\"b\"");
    }

    #[test]
    fn separators() {
        let list = [
            Component::Keyword("a"),
            Component::Comma,
            Component::Keyword("b"),
            Component::Keyword("c"),
            Component::Slash,
            Component::Keyword("d"),
        ];
        assert_eq!(to_string(&list), "a, b c / d");
        assert_eq!(to_string(&[Component::Ident(u("1a"))]), "\\31 a");
    }
}
