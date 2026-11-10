//! The value types the longhands share: CSS Values 4 §5 to §7 (`<number>`, `<integer>`,
//! `<percentage>`, `<length>`, `<length-percentage>`, `<angle>`, with their range
//! restrictions, §2.4†), `<url>` (§4.5†), `<string>` (§4.3†), and the Quirks Mode
//! Standard's `<quirky-length>` (§3.7†).

use super::component::Component;
use super::items::{Cursor, Item, eq_ignore_case, lookup};
use super::number::{ANGLE_UNITS, Angle, LENGTH_UNITS, Length, LengthUnit, Num};

/// Whether a value may be negative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Range {
    /// Any value.
    All,
    /// `[0,∞]`.
    NonNegative,
}

fn in_range(n: Num, range: Range) -> bool {
    range == Range::All || !n.is_negative()
}

/// `<length>` (§6), with the unitless zero (§6: "the unit identifier is optional" for zero);
/// with `quirky`, also `<quirky-length>`: any `<number-token>`, in px.
pub fn length(c: &mut Cursor<'_>, range: Range, quirky: bool) -> Option<Length> {
    let item = c.peek()?;
    let l = match item {
        Item::Dimension { value, unit, .. } => Length {
            value,
            unit: lookup(LENGTH_UNITS, c.src.str(unit))?,
        },
        Item::Number { value, .. } if value.is_zero() || quirky => Length {
            value,
            unit: LengthUnit::Px,
        },
        _ => return None,
    };
    if !in_range(l.value, range) {
        return None;
    }
    c.bump();
    Some(l)
}

/// `<percentage>` (§5.5).
pub fn percentage(c: &mut Cursor<'_>, range: Range) -> Option<Num> {
    match c.peek()? {
        Item::Percentage(p) if in_range(p, range) => {
            c.bump();
            Some(p)
        }
        _ => None,
    }
}

/// `<length-percentage>` (§6.3†), as a component.
pub fn length_percentage(c: &mut Cursor<'_>, range: Range, quirky: bool) -> Option<Component> {
    if let Some(p) = percentage(c, range) {
        return Some(Component::Percentage(p));
    }
    length(c, range, quirky).map(Component::Length)
}

/// `<number>` (§5.4).
pub fn number(c: &mut Cursor<'_>, range: Range) -> Option<Num> {
    match c.peek()? {
        Item::Number { value, .. } if in_range(value, range) => {
            c.bump();
            Some(value)
        }
        _ => None,
    }
}

/// `<angle>` (§7.1); with `zero`, also the unitless zero that some grammars allow.
pub fn angle(c: &mut Cursor<'_>, zero: bool) -> Option<Angle> {
    let a = match c.peek()? {
        Item::Dimension { value, unit, .. } => Angle {
            value,
            unit: lookup(ANGLE_UNITS, c.src.str(unit))?,
        },
        Item::Number { value, .. } if zero && value.is_zero() => Angle {
            value,
            unit: super::number::AngleUnit::Deg,
        },
        _ => return None,
    };
    c.bump();
    Some(a)
}

/// `<url>` (§4.5†): a `<url-token>`, or `url(` or `src(` with one string.
pub fn url(c: &mut Cursor<'_>) -> Option<Vec<u32>> {
    let save = c.pos;
    match c.peek()? {
        Item::Url(s) => {
            c.bump();
            Some(c.src.str(s).to_vec())
        }
        Item::Function { .. } => {
            let (name, mut args) = c.function()?;
            let ok = eq_ignore_case(name, "url") || eq_ignore_case(name, "src");
            let s = match args.bump() {
                Some(Item::String(s)) if ok && args.at_end() => Some(c.src.str(s).to_vec()),
                _ => None,
            };
            if s.is_none() {
                c.pos = save;
            }
            s
        }
        _ => None,
    }
}

/// `<string>` (§4.3†).
pub fn string(c: &mut Cursor<'_>) -> Option<Vec<u32>> {
    match c.peek()? {
        Item::String(s) => {
            c.bump();
            Some(c.src.str(s).to_vec())
        }
        _ => None,
    }
}

/// One of `table`'s keywords, as a component.
pub fn keyword(c: &mut Cursor<'_>, table: &[&'static str]) -> Option<Component> {
    c.keyword(table).map(Component::Keyword)
}

/// `<custom-ident>` (§4.2): any identifier but the CSS-wide keywords and `default`, and
/// those in `excluded`.
pub fn custom_ident(c: &mut Cursor<'_>, excluded: &[&str]) -> Option<Vec<u32>> {
    let save = c.pos;
    let s = c.ident()?;
    if super::is_reserved_ident(s) || excluded.iter().any(|k| eq_ignore_case(s, k)) {
        c.pos = save;
        None
    } else {
        Some(s.to_vec())
    }
}

/// Run `f` on `c`; if it fails, leave `c` where it was.
pub fn attempt<'a, T>(
    c: &mut Cursor<'a>,
    f: impl FnOnce(&mut Cursor<'a>) -> Option<T>,
) -> Option<T> {
    let save = c.pos;
    let r = f(c);
    if r.is_none() {
        c.pos = save;
    }
    r
}

/// `f` applied to the whole of `c`: `None` unless it consumes every item.
pub fn whole<'a, T>(mut c: Cursor<'a>, f: impl FnOnce(&mut Cursor<'a>) -> Option<T>) -> Option<T> {
    let r = f(&mut c)?;
    if c.at_end() { Some(r) } else { None }
}
