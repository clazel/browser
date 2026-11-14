//! The flow-relative margin, padding and border properties (CSS Logical Properties 1,
//! Editor's Draft†, §4.1 to §4.4† and §6†), mapped to the physical longhands of the subset.
//!
//! HTML §15's user agent style sheet writes its margins and paddings with them
//! (`margin-block: 1em`, `padding-inline-start: 40px`, `border-block-style: solid`), and
//! `values/` knows only the physical properties. CSS Logical 1 §4† says each logical
//! property and its physical counterpart "share a computed value", the one declared later
//! (in cascade order) winning, which is the effect of mapping a logical declaration to its
//! physical longhands before the cascade, given the writing mode. Phase 5 has one writing
//! mode: `writing-mode` and `direction` are not in the subset (bidirectional text is Phase
//! 8's), so every element is `horizontal-tb` and `ltr`: block-start is top, block-end
//! bottom, inline-start left and inline-end right (CSS Writing Modes 4 §6.4†'s table).
//!
//! The grammars: `margin-block-start` and the other single-side longhands take their
//! physical longhand's grammar; `margin-block`, `margin-inline`, `padding-block`,
//! `padding-inline`, `border-block-width`, `-style`, `-color` and their `inline` forms take
//! one or two values of it, start then end ("If the second value is omitted, it is copied
//! from the first", §4.2†); `border-block-start` and the other single-side `border`
//! shorthands take `border-top`'s; and `border-block` and `border-inline` set both sides
//! to one `border-top` value (§6†). The quirks never apply: their lists name only physical
//! properties.

use crate::values::items::{Cursor, Src, eq_ignore_case};
use crate::values::longhand::Longhand;
use crate::values::shorthand::Shorthand;
use crate::values::{Declared, Property, Specified, grammar, parse_items};

/// A physical side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Top,
    Right,
    Bottom,
    Left,
}

/// The sides of an axis, start then end, in `horizontal-tb` and `ltr`.
fn sides(axis: &[u32]) -> Option<[Side; 2]> {
    if eq_ignore_case(axis, "block") {
        Some([Side::Top, Side::Bottom])
    } else if eq_ignore_case(axis, "inline") {
        Some([Side::Left, Side::Right])
    } else {
        None
    }
}

/// What a logical property is made of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Part {
    Margin,
    Padding,
    BorderWidth,
    BorderStyle,
    BorderColor,
    /// A `border-*` shorthand of one side (`border-top`'s grammar).
    Border,
}

/// The physical longhand of `part` on `side`.
fn longhand(part: Part, side: Side) -> Option<Longhand> {
    use Longhand as L;
    let [t, r, b, l] = match part {
        Part::Margin => [L::MarginTop, L::MarginRight, L::MarginBottom, L::MarginLeft],
        Part::Padding => [
            L::PaddingTop,
            L::PaddingRight,
            L::PaddingBottom,
            L::PaddingLeft,
        ],
        Part::BorderWidth => [
            L::BorderTopWidth,
            L::BorderRightWidth,
            L::BorderBottomWidth,
            L::BorderLeftWidth,
        ],
        Part::BorderStyle => [
            L::BorderTopStyle,
            L::BorderRightStyle,
            L::BorderBottomStyle,
            L::BorderLeftStyle,
        ],
        Part::BorderColor => [
            L::BorderTopColor,
            L::BorderRightColor,
            L::BorderBottomColor,
            L::BorderLeftColor,
        ],
        Part::Border => return None,
    };
    Some(match side {
        Side::Top => t,
        Side::Right => r,
        Side::Bottom => b,
        Side::Left => l,
    })
}

/// The physical `border-*` shorthand of `side`.
fn border_shorthand(side: Side) -> Shorthand {
    match side {
        Side::Top => Shorthand::BorderTop,
        Side::Right => Shorthand::BorderRight,
        Side::Bottom => Shorthand::BorderBottom,
        Side::Left => Shorthand::BorderLeft,
    }
}

/// A logical property's name read: its part, its axis's sides, and which of them (`None`
/// for both).
fn read_name(name: &[u32]) -> Option<(Part, [Side; 2], Option<usize>)> {
    let words: Vec<&[u32]> = name.split(|&c| c == 0x2D).collect();
    let word = |i: usize| words.get(i).copied().unwrap_or_default();
    let (base, rest): (&[u32], usize) = (word(0), 1);
    let axis = sides(word(rest))?;
    let mut next = rest.saturating_add(1);
    let which = if eq_ignore_case(word(next), "start") {
        next = next.saturating_add(1);
        Some(0)
    } else if eq_ignore_case(word(next), "end") {
        next = next.saturating_add(1);
        Some(1)
    } else {
        None
    };
    let last = word(next);
    let part = if eq_ignore_case(base, "margin") && last.is_empty() {
        Part::Margin
    } else if eq_ignore_case(base, "padding") && last.is_empty() {
        Part::Padding
    } else if eq_ignore_case(base, "border") {
        if last.is_empty() {
            Part::Border
        } else if eq_ignore_case(last, "width") {
            Part::BorderWidth
        } else if eq_ignore_case(last, "style") {
            Part::BorderStyle
        } else if eq_ignore_case(last, "color") {
            Part::BorderColor
        } else {
            return None;
        }
    } else {
        return None;
    };
    // Nothing may follow the last word.
    let used = if last.is_empty() {
        next
    } else {
        next.saturating_add(1)
    };
    (words.len() == used).then_some((part, axis, which))
}

/// The physical declarations a declaration of the logical property `name` with the value
/// `src` sets; `None` if `name` is not one of them or the value is invalid for it.
pub fn parse(name: &[u32], src: Src<'_>) -> Option<Vec<Declared>> {
    let (part, axis, which) = read_name(name)?;
    let [start, end] = axis;
    if part == Part::Border {
        // `border-block-start`: `border-top`'s grammar on its side; `border-block`: one such
        // value on both sides.
        let chosen: Vec<Side> = match which {
            Some(0) => vec![start],
            Some(_) => vec![end],
            None => vec![start, end],
        };
        let mut out = Vec::new();
        for side in chosen {
            let p = Property::Shorthand(border_shorthand(side));
            out.extend(parse_items(p, src, false)?);
        }
        return Some(out);
    }
    let one = |side: Side| longhand(part, side);
    if let Some(w) = which {
        let side = if w == 0 { start } else { end };
        return parse_items(Property::Longhand(one(side)?), src, false);
    }
    // The two-value forms: a CSS-wide keyword is the whole value and sets both sides.
    let (ls, le) = (one(start)?, one(end)?);
    if let Some(d) = parse_items(Property::Longhand(ls), src, false)
        && let Some(Declared {
            value: Specified::Wide(w),
            ..
        }) = d.first()
    {
        let w = *w;
        return Some(vec![
            Declared {
                property: ls,
                value: Specified::Wide(w),
            },
            Declared {
                property: le,
                value: Specified::Wide(w),
            },
        ]);
    }
    let mut c = Cursor::new(src);
    let first = ls.parse(&mut c, false)?;
    let second = if c.at_end() {
        first.clone()
    } else {
        grammar::attempt(&mut c, |c| le.parse(c, false))?
    };
    c.at_end().then(|| {
        vec![
            Declared {
                property: ls,
                value: Specified::Value(first),
            },
            Declared {
                property: le,
                value: Specified::Value(second),
            },
        ]
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::items::Values;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn set(name: &str, value: &str) -> Option<Vec<(Longhand, String)>> {
        let v = Values::parse(&u(value))?;
        let out = parse(&u(name), v.src())?;
        Some(
            out.into_iter()
                .map(|d| {
                    let s = match d.value {
                        Specified::Wide(w) => w.name().to_owned(),
                        Specified::Value(c) => crate::values::component::to_string(&c),
                    };
                    (d.property, s)
                })
                .collect(),
        )
    }

    #[test]
    fn maps_to_physical() {
        use Longhand as L;
        assert_eq!(
            set("margin-block", "1em"),
            Some(vec![
                (L::MarginTop, "1em".into()),
                (L::MarginBottom, "1em".into())
            ])
        );
        assert_eq!(
            set("margin-inline", "auto 2px"),
            Some(vec![
                (L::MarginLeft, "auto".into()),
                (L::MarginRight, "2px".into())
            ])
        );
        assert_eq!(
            set("padding-inline-start", "40px"),
            Some(vec![(L::PaddingLeft, "40px".into())])
        );
        assert_eq!(
            set("margin-block-end", "inherit"),
            Some(vec![(L::MarginBottom, "inherit".into())])
        );
        assert_eq!(
            set("border-block-style", "none"),
            Some(vec![
                (L::BorderTopStyle, "none".into()),
                (L::BorderBottomStyle, "none".into())
            ])
        );
        assert_eq!(
            set("border-inline-width", "1px"),
            Some(vec![
                (L::BorderLeftWidth, "1px".into()),
                (L::BorderRightWidth, "1px".into())
            ])
        );
        assert_eq!(
            set("margin-block", "unset"),
            Some(vec![
                (L::MarginTop, "unset".into()),
                (L::MarginBottom, "unset".into())
            ])
        );
        assert_eq!(
            set("border-block-start", "1px solid red").map(|v| v.len()),
            Some(3)
        );
        assert_eq!(set("border-inline", "thin").map(|v| v.len()), Some(6));
        assert_eq!(set("margin-block", "1px 2px 3px"), None);
        assert_eq!(set("margin-blocks", "1px"), None);
        assert_eq!(set("margin-block-start-x", "1px"), None);
        assert_eq!(set("inset-block", "0"), None);
        assert_eq!(set("padding-block", "-1px"), None);
    }
}
