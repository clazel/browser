//! The shorthands of the subset: their grammars, their expansion into longhands ("a
//! shorthand sets all of its longhands; those it omits are set to their initial value",
//! CSS Cascade 4 §1.2†), and CSSOM's serialization of a shorthand from its longhands
//! ("serialize a CSS value" for a shorthand†: the shortest form that sets them all, or the
//! empty string if none does).

use super::color::{Color, parse_color};
use super::component::{Component, has_top_level_comma, to_string};
use super::grammar::{attempt, keyword};
use super::items::Cursor;
use super::longhand::{
    LINE_STYLES, Longhand as L, VISUAL_BOXES, bg_position, bg_size, font_size, font_stretch,
    font_style, font_weight, image, line_height, repeat_style, text_decoration_line,
};

macro_rules! shorthands {
    ($($variant:ident = $name:literal: [$($l:ident),*],)*) => {
        /// A shorthand property of the subset.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[cfg_attr(kani, derive(kani::Arbitrary))]
        pub enum Shorthand {
            $(#[doc = concat!("`", $name, "`.")] $variant,)*
        }

        /// Every shorthand, with its name.
        pub const SHORTHANDS: &[(&str, Shorthand)] = &[$(($name, Shorthand::$variant),)*];

        impl Shorthand {
            /// The longhands it sets, in its canonical order.
            pub fn longhands(self) -> &'static [L] {
                match self {
                    $(Shorthand::$variant => &[$(L::$l),*],)*
                }
            }
        }
    };
}

shorthands! {
    // CSS Box 3 §5.2†.
    Margin = "margin": [MarginTop, MarginRight, MarginBottom, MarginLeft],
    // CSS Box 3 §6.2†.
    Padding = "padding": [PaddingTop, PaddingRight, PaddingBottom, PaddingLeft],
    // CSS Backgrounds 3 §3.3† to §3.5†.
    BorderWidth = "border-width": [BorderTopWidth, BorderRightWidth, BorderBottomWidth, BorderLeftWidth],
    BorderStyle = "border-style": [BorderTopStyle, BorderRightStyle, BorderBottomStyle, BorderLeftStyle],
    BorderColor = "border-color": [BorderTopColor, BorderRightColor, BorderBottomColor, BorderLeftColor],
    // CSS Backgrounds 3 §3.6†.
    BorderTop = "border-top": [BorderTopWidth, BorderTopStyle, BorderTopColor],
    BorderRight = "border-right": [BorderRightWidth, BorderRightStyle, BorderRightColor],
    BorderBottom = "border-bottom": [BorderBottomWidth, BorderBottomStyle, BorderBottomColor],
    BorderLeft = "border-left": [BorderLeftWidth, BorderLeftStyle, BorderLeftColor],
    Border = "border": [
        BorderTopWidth, BorderTopStyle, BorderTopColor,
        BorderRightWidth, BorderRightStyle, BorderRightColor,
        BorderBottomWidth, BorderBottomStyle, BorderBottomColor,
        BorderLeftWidth, BorderLeftStyle, BorderLeftColor
    ],
    // CSS Backgrounds 3 §2.11†.
    Background = "background": [
        BackgroundColor, BackgroundImage, BackgroundPosition, BackgroundSize,
        BackgroundRepeat, BackgroundAttachment, BackgroundOrigin, BackgroundClip
    ],
    // CSS Overflow 3 §3.1†.
    Overflow = "overflow": [OverflowX, OverflowY],
    // CSS Fonts 4 §2.8†.
    Font = "font": [FontStyle, FontVariantCaps, FontWeight, FontStretch, FontSize, LineHeight, FontFamily],
    // CSS Text Decoration 3 §2.4† (with Level 4's thickness).
    TextDecoration = "text-decoration": [TextDecorationLine, TextDecorationThickness, TextDecorationStyle, TextDecorationColor],
}

impl Shorthand {
    /// The shorthand's name.
    pub fn name(self) -> &'static str {
        SHORTHANDS
            .iter()
            .find(|(_, s)| *s == self)
            .map_or("", |(n, _)| n)
    }
}

/// One to four values of `longhand`'s grammar, for top, right, bottom and left (CSS
/// Backgrounds 3 §1.1† "the usual 1-to-4 value syntax").
fn four(c: &mut Cursor<'_>, longhand: L, quirks: bool) -> Option<[Vec<Component>; 4]> {
    let mut v: Vec<Vec<Component>> = Vec::new();
    for _ in 0..4 {
        if c.at_end() {
            break;
        }
        v.push(longhand.parse(c, quirks)?);
    }
    let get = |i: usize| v.get(i).cloned();
    let top = get(0)?;
    let right = get(1).unwrap_or_else(|| top.clone());
    let bottom = get(2).unwrap_or_else(|| top.clone());
    let left = get(3).unwrap_or_else(|| right.clone());
    Some([top, right, bottom, left])
}

/// `<line-width> || <line-style> || <color>` (CSS Backgrounds 3 §3.6†), with the omitted
/// parts initial. Neither quirk applies in a shorthand of this form (the Quirks Mode
/// Standard lists only `border-width` and `border-color` among the border shorthands).
fn border_side(c: &mut Cursor<'_>) -> Option<[Vec<Component>; 3]> {
    let mut width = None;
    let mut style = None;
    let mut color = None;
    for _ in 0..c.budget() {
        if c.at_end() {
            break;
        }
        if width.is_none()
            && let Some(w) = attempt(c, |c| L::BorderTopWidth.parse(c, false))
        {
            width = Some(w);
            continue;
        }
        if style.is_none()
            && let Some(s) = keyword(c, LINE_STYLES)
        {
            style = Some(vec![s]);
            continue;
        }
        if color.is_none()
            && let Some(col) = parse_color(c, false)
        {
            color = Some(vec![Component::Color(col)]);
            continue;
        }
        return None;
    }
    if !c.at_end() {
        return None;
    }
    if width.is_none() && style.is_none() && color.is_none() {
        return None;
    }
    Some([
        width.unwrap_or_else(|| L::BorderTopWidth.initial()),
        style.unwrap_or_else(|| L::BorderTopStyle.initial()),
        color.unwrap_or_else(|| L::BorderTopColor.initial()),
    ])
}

/// `text-decoration` (CSS Text Decoration 4 §2.5†): `<'text-decoration-line'> ||
/// <'text-decoration-thickness'> || <'text-decoration-style'> || <'text-decoration-color'>`.
fn text_decoration(c: &mut Cursor<'_>) -> Option<[Vec<Component>; 4]> {
    let mut parts: [Option<Vec<Component>>; 4] = [None, None, None, None];
    for _ in 0..c.budget() {
        if c.at_end() {
            break;
        }
        let [line, thickness, style, color] = &mut parts;
        if line.is_none()
            && let Some(v) = attempt(c, text_decoration_line)
        {
            *line = Some(v);
            continue;
        }
        if thickness.is_none()
            && let Some(v) = attempt(c, |c| L::TextDecorationThickness.parse(c, false))
        {
            *thickness = Some(v);
            continue;
        }
        if style.is_none()
            && let Some(v) = attempt(c, |c| L::TextDecorationStyle.parse(c, false))
        {
            *style = Some(v);
            continue;
        }
        if color.is_none()
            && let Some(col) = parse_color(c, false)
        {
            *color = Some(vec![Component::Color(col)]);
            continue;
        }
        return None;
    }
    if !c.at_end() {
        return None;
    }
    if parts.iter().all(Option::is_none) {
        return None;
    }
    let [line, thickness, style, color] = parts;
    Some([
        line.unwrap_or_else(|| L::TextDecorationLine.initial()),
        thickness.unwrap_or_else(|| L::TextDecorationThickness.initial()),
        style.unwrap_or_else(|| L::TextDecorationStyle.initial()),
        color.unwrap_or_else(|| L::TextDecorationColor.initial()),
    ])
}

/// `font` (CSS Fonts 4 §2.8†): `[ <'font-style'> || <font-variant-css2> || <'font-weight'>
/// || <font-width-css3> ]? <'font-size'> [ / <'line-height'> ]? <'font-family'>#`. Each
/// `normal` fills one of the four optional parts. The system font keywords are not in the
/// subset. Neither quirk applies within `font` (Quirks Mode §3.7† lists `font-size`, not
/// `font`; WPT's `font:normal normal normal 40 sans-serif` checks it).
fn font(c: &mut Cursor<'_>) -> Option<[Vec<Component>; 7]> {
    let mut style = None;
    let mut variant = None;
    let mut weight = None;
    let mut stretch = None;
    let mut normals = 0usize;
    for _ in 0..4 {
        if c.eat_keyword("normal") {
            normals = normals.saturating_add(1);
            continue;
        }
        if style.is_none()
            && let Some(v) = attempt(c, font_style)
        {
            style = Some(v);
            continue;
        }
        if variant.is_none() && c.eat_keyword("small-caps") {
            variant = Some(vec![Component::Keyword("small-caps")]);
            continue;
        }
        if weight.is_none()
            && let Some(v) = attempt(c, font_weight)
        {
            weight = Some(v);
            continue;
        }
        if stretch.is_none() {
            let save = c.pos;
            if let Some(v) = font_stretch(c) {
                // Only the CSS 3 keywords, not a percentage, before the size.
                if matches!(v.first(), Some(Component::Keyword(_))) {
                    stretch = Some(v);
                    continue;
                }
                c.pos = save;
            }
        }
        break;
    }
    let given = [&style, &variant, &weight, &stretch]
        .iter()
        .filter(|p| p.is_some())
        .count();
    if given.saturating_add(normals) > 4 {
        return None;
    }
    let size = font_size(c, false)?;
    let line = if c.delim(0x2F) {
        line_height(c)?
    } else {
        L::LineHeight.initial()
    };
    let family = L::FontFamily.parse(c, false)?;
    Some([
        style.unwrap_or_else(|| L::FontStyle.initial()),
        variant.unwrap_or_else(|| L::FontVariantCaps.initial()),
        weight.unwrap_or_else(|| L::FontWeight.initial()),
        stretch.unwrap_or_else(|| L::FontStretch.initial()),
        size,
        line,
        family,
    ])
}

/// `background` (CSS Backgrounds 3 §2.11†), one layer: `<'background-color'> || <bg-image>
/// || <bg-position> [ / <bg-size> ]? || <repeat-style> || <attachment> || <visual-box> ||
/// <visual-box>`. One box sets both origin and clip; two set origin, then clip. Several
/// layers are not in the subset.
fn background(c: &mut Cursor<'_>) -> Option<[Vec<Component>; 8]> {
    let mut color: Option<Color> = None;
    let mut img = None;
    let mut position = None;
    let mut size = None;
    let mut repeat = None;
    let mut attachment = None;
    let mut boxes: Vec<Component> = Vec::new();
    for _ in 0..c.budget() {
        if c.at_end() {
            break;
        }
        if img.is_none() {
            if let Some(k) = keyword(c, &["none"]) {
                img = Some(vec![k]);
                continue;
            }
            if let Some(i) = image(c) {
                img = Some(i);
                continue;
            }
        }
        if position.is_none()
            && let Some(p) = attempt(c, |c| bg_position(c, false))
        {
            position = Some(p);
            if c.delim(0x2F) {
                size = Some(bg_size(c)?);
            }
            continue;
        }
        if repeat.is_none()
            && let Some(r) = attempt(c, repeat_style)
        {
            repeat = Some(r);
            continue;
        }
        if attachment.is_none()
            && let Some(a) = keyword(c, &["scroll", "fixed", "local"])
        {
            attachment = Some(vec![a]);
            continue;
        }
        if boxes.len() < 2
            && let Some(b) = keyword(c, VISUAL_BOXES)
        {
            boxes.push(b);
            continue;
        }
        if color.is_none()
            && let Some(col) = parse_color(c, false)
        {
            color = Some(col);
            continue;
        }
        return None;
    }
    if !c.at_end() {
        return None;
    }
    let (origin, clip) = match boxes.as_slice() {
        [] => (L::BackgroundOrigin.initial(), L::BackgroundClip.initial()),
        [one] => (vec![one.clone()], vec![one.clone()]),
        [o, k, ..] => (vec![o.clone()], vec![k.clone()]),
    };
    Some([
        color.map_or_else(
            || L::BackgroundColor.initial(),
            |c| vec![Component::Color(c)],
        ),
        img.unwrap_or_else(|| L::BackgroundImage.initial()),
        position.unwrap_or_else(|| L::BackgroundPosition.initial()),
        size.unwrap_or_else(|| L::BackgroundSize.initial()),
        repeat.unwrap_or_else(|| L::BackgroundRepeat.initial()),
        attachment.unwrap_or_else(|| L::BackgroundAttachment.initial()),
        origin,
        clip,
    ])
}

impl Shorthand {
    /// Read the shorthand's value from `c` and expand it: one value per longhand, in the
    /// order of [`Shorthand::longhands`]. The caller checks that nothing is left.
    pub fn parse(self, c: &mut Cursor<'_>, quirks: bool) -> Option<Vec<Vec<Component>>> {
        use Shorthand as S;
        let v: Vec<Vec<Component>> = match self {
            S::Margin => four(c, L::MarginTop, quirks)?.into(),
            S::Padding => four(c, L::PaddingTop, quirks)?.into(),
            S::BorderWidth => four(c, L::BorderTopWidth, quirks)?.into(),
            S::BorderStyle => four(c, L::BorderTopStyle, quirks)?.into(),
            S::BorderColor => four(c, L::BorderTopColor, quirks)?.into(),
            S::BorderTop | S::BorderRight | S::BorderBottom | S::BorderLeft => {
                border_side(c)?.into()
            }
            S::Border => {
                let side: Vec<Vec<Component>> = border_side(c)?.into();
                let mut all = Vec::new();
                for _ in 0..4 {
                    all.extend(side.iter().cloned());
                }
                all
            }
            S::Background => background(c)?.into(),
            S::Overflow => {
                let x = L::OverflowX.parse(c, quirks)?;
                let y = if c.at_end() {
                    x.clone()
                } else {
                    L::OverflowY.parse(c, quirks)?
                };
                vec![x, y]
            }
            S::Font => font(c)?.into(),
            S::TextDecoration => text_decoration(c)?.into(),
        };
        Some(v)
    }

    /// CSSOM's serialization of the shorthand from its longhands' values, given in the
    /// order of [`Shorthand::longhands`]; `None` if no value of the shorthand sets them so
    /// (then CSSOM gives the empty string).
    pub fn serialize(self, values: &[Vec<Component>]) -> Option<String> {
        use Shorthand as S;
        let get = |i: usize| values.get(i);
        match self {
            S::Margin | S::Padding | S::BorderWidth | S::BorderStyle | S::BorderColor => {
                let [t, r, b, l] = [get(0)?, get(1)?, get(2)?, get(3)?];
                let parts: &[&Vec<Component>] = if l != r {
                    &[t, r, b, l]
                } else if b != t {
                    &[t, r, b]
                } else if r != t {
                    &[t, r]
                } else {
                    &[t]
                };
                Some(join(parts))
            }
            S::BorderTop | S::BorderRight | S::BorderBottom | S::BorderLeft => {
                Some(serialize_side([get(0)?, get(1)?, get(2)?]))
            }
            S::Border => {
                let first = [get(0)?, get(1)?, get(2)?];
                for side in 1..4usize {
                    let at = side.saturating_mul(3);
                    let this = [
                        get(at)?,
                        get(at.saturating_add(1))?,
                        get(at.saturating_add(2))?,
                    ];
                    if this != first {
                        return None;
                    }
                }
                Some(serialize_side(first))
            }
            S::Overflow => {
                let (x, y) = (get(0)?, get(1)?);
                Some(if x == y { join(&[x]) } else { join(&[x, y]) })
            }
            S::TextDecoration => {
                let [line, thickness, style, color] = [get(0)?, get(1)?, get(2)?, get(3)?];
                let mut parts = Vec::new();
                if *line != L::TextDecorationLine.initial() {
                    parts.push(line);
                }
                if *thickness != L::TextDecorationThickness.initial() {
                    parts.push(thickness);
                }
                if *style != L::TextDecorationStyle.initial() {
                    parts.push(style);
                }
                if *color != L::TextDecorationColor.initial() {
                    parts.push(color);
                }
                Some(if parts.is_empty() {
                    "none".to_owned()
                } else {
                    join(&parts)
                })
            }
            S::Font => {
                let [style, variant, weight, stretch, size, line, family] = [
                    get(0)?,
                    get(1)?,
                    get(2)?,
                    get(3)?,
                    get(4)?,
                    get(5)?,
                    get(6)?,
                ];
                // `font` can only set the CSS 2.1 variant and the keyword widths.
                let variant_ok = *variant == L::FontVariantCaps.initial()
                    || *variant == vec![Component::Keyword("small-caps")];
                let stretch_ok = matches!(stretch.first(), Some(Component::Keyword(_)));
                if !variant_ok || !stretch_ok {
                    return None;
                }
                let mut out = String::new();
                for (part, longhand) in [
                    (style, L::FontStyle),
                    (variant, L::FontVariantCaps),
                    (weight, L::FontWeight),
                    (stretch, L::FontStretch),
                ] {
                    if *part != longhand.initial() {
                        out.push_str(&to_string(part));
                        out.push(' ');
                    }
                }
                out.push_str(&to_string(size));
                if *line != L::LineHeight.initial() {
                    out.push_str(" / ");
                    out.push_str(&to_string(line));
                }
                out.push(' ');
                out.push_str(&to_string(family));
                Some(out)
            }
            S::Background => {
                let longhands = self.longhands();
                let mut parts: Vec<String> = Vec::new();
                let initial = |i: usize| {
                    longhands
                        .get(i)
                        .is_some_and(|l| values.get(i) == Some(&l.initial()))
                };
                // A list value (several layers) is not one layer.
                if values.iter().any(|v| has_top_level_comma(v)) {
                    return None;
                }
                // CSS Backgrounds 3's order, colour first as WebKit and the text give it.
                if !initial(0) {
                    parts.push(to_string(get(0)?));
                }
                if !initial(1) {
                    parts.push(to_string(get(1)?));
                }
                if !initial(2) || !initial(3) {
                    let mut p = to_string(get(2)?);
                    if !initial(3) {
                        p.push_str(" / ");
                        p.push_str(&to_string(get(3)?));
                    }
                    parts.push(p);
                }
                for i in [4usize, 5] {
                    if !initial(i) {
                        parts.push(to_string(get(i)?));
                    }
                }
                let (origin, clip) = (get(6)?, get(7)?);
                if !(initial(6) && initial(7)) {
                    if origin == clip {
                        parts.push(to_string(origin));
                    } else {
                        parts.push(to_string(origin));
                        parts.push(to_string(clip));
                    }
                }
                Some(if parts.is_empty() {
                    "none".to_owned()
                } else {
                    parts.join(" ")
                })
            }
        }
    }
}

/// `width style color`, leaving out the initial ones but never all of them.
fn serialize_side(side: [&Vec<Component>; 3]) -> String {
    let [w, s, col] = side;
    let mut parts = Vec::new();
    if *w != L::BorderTopWidth.initial() {
        parts.push(w);
    }
    if *s != L::BorderTopStyle.initial() {
        parts.push(s);
    }
    if *col != L::BorderTopColor.initial() {
        parts.push(col);
    }
    if parts.is_empty() {
        parts.push(s);
    }
    join(&parts)
}

fn join(parts: &[&Vec<Component>]) -> String {
    parts
        .iter()
        .map(|p| to_string(p))
        .collect::<Vec<_>>()
        .join(" ")
}
