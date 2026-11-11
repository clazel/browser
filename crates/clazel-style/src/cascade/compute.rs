//! CSS Cascade 4 §4.3 to §4.4 and §7: from each property's cascaded value on an element to
//! its specified value (defaulting) and its computed value.
//!
//! §4.3 "Specified Values": "If the cascade results in a value, use it as the specified
//! value. Otherwise, if the property is inherited and the element is not the root of the
//! document tree, use the computed value of the parent element. Otherwise, use the
//! property's initial value." §7.3 gives the CSS-wide keywords: `initial` is the initial
//! value, `inherit` the inherited value ("the computed value of the property on the
//! element's parent element. For the root element, which has no parent element, the
//! inherited value is the initial value of the property", §7.2), `unset` `inherit` for an
//! inherited property and `initial` otherwise. `revert` and `revert-layer` are resolved by
//! the cascade (`sort.rs`) before this.
//!
//! §4.4 "Computed Values": each property's "Computed value" line, which
//! [`super::computed::ComputedStyle`]'s fields quote. The dependencies between properties are
//! taken in order: `font-size` first (its `em` and percentages refer to the parent's font
//! size, CSS Fonts 4 §2.4†, and every other `em` to the element's own, CSS Values 4 §6.1.1†),
//! then `color` (which `currentcolor` refers to, CSS Color 4 §4.4†), then the rest; then the
//! rules that read two properties (border widths and styles, `overflow-x` and
//! `overflow-y`) and the root element's blockification.
//!
//! A cascaded value comes from `values/`, which only builds values of the property's
//! grammar; a value this module cannot read (which would be a mismatch between the two
//! modules) leaves the property defaulted, as if the declaration were invalid.

use super::computed::{
    BLACK, ComputedStyle, DecorationLines, DecorationStyle, Display, Family, FontStyle, LineHeight,
    LineStyle, ListStyleType, Lp, MEDIUM_PX64, MaxSize, Overflow, OverflowWrap, Rgba, Size,
    TextAlign, TextIndent, VerticalAlign, Visibility, WhiteSpace, WordBreak,
};
use crate::values::Specified;
use crate::values::Wide;
use crate::values::color::Color;
use crate::values::component::Component;
use crate::values::longhand::{LONGHANDS, Longhand};
use crate::values::number::{MAX_PX64, Num, SCALE, degrees, percentage_px64, to_px64};

/// The number of longhands.
pub const LONGHAND_COUNT: usize = LONGHANDS.len();

/// A longhand's index in [`LONGHANDS`] (the enum's order).
pub fn index(l: Longhand) -> usize {
    l as usize
}

/// True for the inherited properties of the subset: those whose definition table says
/// "Inherited: yes" (CSS Color 4 `color`; CSS Fonts 4 `font-*`; CSS Inline 3 / CSS 2.1
/// `line-height`; CSS Text 3 `text-align`, `text-indent`, `white-space`, `overflow-wrap`,
/// `word-break`; CSS 2.1 `visibility`, `border-collapse`, `border-spacing`; CSS Lists 3
/// `list-style-type`; CSS UI 4 `cursor` and `pointer-events`). Every other longhand is not
/// inherited.
pub fn inherited(l: Longhand) -> bool {
    use Longhand as L;
    matches!(
        l,
        L::Color
            | L::FontFamily
            | L::FontSize
            | L::FontWeight
            | L::FontStyle
            | L::FontVariantCaps
            | L::FontStretch
            | L::LineHeight
            | L::TextAlign
            | L::TextIndent
            | L::WhiteSpace
            | L::OverflowWrap
            | L::WordBreak
            | L::Visibility
            | L::BorderCollapse
            | L::BorderSpacing
            | L::ListStyleType
            | L::Cursor
            | L::PointerEvents
    )
}

/// What computing an element's values reads besides its cascaded values.
pub struct Context<'a> {
    /// The parent element's computed style; the initial style for the root (§7.2).
    pub parent: &'a ComputedStyle,
    /// The root element's computed `font-size` in 1/64 px, which `rem` refers to (CSS Values
    /// 4 §6.1.1†); for the root itself, the initial font size.
    pub root_font_size: i32,
    /// True for the root element.
    pub is_root: bool,
    /// The family lists so far, which a computed `font-family` is added to.
    pub families: &'a mut Vec<Vec<Family>>,
}

/// The absolute-size keywords' sizes in px for a `medium` of 16 px (CSS Fonts 4 §2.5.1†'s
/// table of scaling factors, "The user agent may fine-tune these values"): the sizes every
/// engine uses, the same as HTML's legacy `font` sizes 1 to 7 give.
const ABSOLUTE_SIZES: &[(&str, i32)] = &[
    ("xx-small", 9),
    ("x-small", 10),
    ("small", 13),
    ("medium", 16),
    ("large", 18),
    ("x-large", 24),
    ("xx-large", 32),
    ("xxx-large", 48),
];

/// `a * num / den`, rounded to nearest, clamped to `0 ..= MAX_PX64`.
fn scale(a: i32, num: i64, den: i64) -> i32 {
    let n = i64::from(a).saturating_mul(num);
    let q = n
        .saturating_add(den.checked_div(2).unwrap_or(0))
        .checked_div(den)
        .unwrap_or(0);
    i32::try_from(q.clamp(0, i64::from(MAX_PX64))).unwrap_or(0)
}

/// CSS Values 4 §6.5†, "snap as a border width", with one device pixel per CSS pixel: "If
/// len is an integer number of device pixels, do nothing. If len is greater than zero, but
/// less than 1 device pixel, round len up to 1 device pixel. If len is greater than 1
/// device pixel, round it down to the nearest integer number of device pixels."
pub fn snap_border_width(px64: i32) -> i32 {
    if px64 <= 0 {
        0
    } else if px64 < 64 {
        64
    } else {
        px64.saturating_sub(px64.checked_rem(64).unwrap_or(0))
    }
}

fn keyword(v: &[Component]) -> Option<&'static str> {
    match v {
        [Component::Keyword(k)] => Some(k),
        _ => None,
    }
}

fn find<T: Copy>(table: &[(&str, T)], k: &str) -> Option<T> {
    table.iter().find(|(n, _)| *n == k).map(|(_, t)| *t)
}

/// A computed `<length-percentage>`, its `em` against `em_px64`.
fn lp(c: &Component, em_px64: i32, rem_px64: i32) -> Option<Lp> {
    match c {
        Component::Length(l) => Some(Lp::Px64(to_px64(*l, em_px64, rem_px64))),
        Component::Percentage(p) => Some(Lp::Percent(*p)),
        _ => None,
    }
}

/// A length's 1/64 px.
fn length(c: &Component, em_px64: i32, rem_px64: i32) -> Option<i32> {
    match c {
        Component::Length(l) => Some(to_px64(*l, em_px64, rem_px64)),
        _ => None,
    }
}

/// A colour, with `currentcolor` as `current`.
fn color(v: &[Component], current: Rgba) -> Option<Rgba> {
    match v {
        [Component::Color(Color::CurrentColor)] => Some(current),
        [Component::Color(c)] => c.rgba(),
        _ => None,
    }
}

const LINE_STYLES: &[(&str, LineStyle)] = &[
    ("none", LineStyle::None),
    ("hidden", LineStyle::Hidden),
    ("dotted", LineStyle::Dotted),
    ("dashed", LineStyle::Dashed),
    ("solid", LineStyle::Solid),
    ("double", LineStyle::Double),
    ("groove", LineStyle::Groove),
    ("ridge", LineStyle::Ridge),
    ("inset", LineStyle::Inset),
    ("outset", LineStyle::Outset),
];

const DISPLAYS: &[(&str, Display)] = &[
    ("none", Display::None),
    ("block", Display::Block),
    ("inline", Display::Inline),
    ("inline-block", Display::InlineBlock),
    ("list-item", Display::ListItem),
    ("table", Display::Table),
    ("inline-table", Display::InlineTable),
    ("table-row-group", Display::TableRowGroup),
    ("table-header-group", Display::TableHeaderGroup),
    ("table-footer-group", Display::TableFooterGroup),
    ("table-row", Display::TableRow),
    ("table-cell", Display::TableCell),
    ("table-column-group", Display::TableColumnGroup),
    ("table-column", Display::TableColumn),
    ("table-caption", Display::TableCaption),
];

const OVERFLOWS: &[(&str, Overflow)] = &[
    ("visible", Overflow::Visible),
    ("hidden", Overflow::Hidden),
    ("clip", Overflow::Clip),
    ("scroll", Overflow::Scroll),
    ("auto", Overflow::Auto),
];

const VISIBILITIES: &[(&str, Visibility)] = &[
    ("visible", Visibility::Visible),
    ("hidden", Visibility::Hidden),
    ("collapse", Visibility::Collapse),
];

const VERTICAL_ALIGNS: &[(&str, VerticalAlign)] = &[
    ("baseline", VerticalAlign::Baseline),
    ("sub", VerticalAlign::Sub),
    ("super", VerticalAlign::Super),
    ("top", VerticalAlign::Top),
    ("text-top", VerticalAlign::TextTop),
    ("middle", VerticalAlign::Middle),
    ("bottom", VerticalAlign::Bottom),
    ("text-bottom", VerticalAlign::TextBottom),
];

const TEXT_ALIGNS: &[(&str, TextAlign)] = &[
    ("start", TextAlign::Start),
    ("end", TextAlign::End),
    ("left", TextAlign::Left),
    ("right", TextAlign::Right),
    ("center", TextAlign::Center),
    ("justify", TextAlign::Justify),
    ("justify-all", TextAlign::JustifyAll),
];

const DECORATION_STYLES: &[(&str, DecorationStyle)] = &[
    ("solid", DecorationStyle::Solid),
    ("double", DecorationStyle::Double),
    ("dotted", DecorationStyle::Dotted),
    ("dashed", DecorationStyle::Dashed),
    ("wavy", DecorationStyle::Wavy),
];

const WHITE_SPACES: &[(&str, WhiteSpace)] = &[
    ("normal", WhiteSpace::Normal),
    ("pre", WhiteSpace::Pre),
    ("nowrap", WhiteSpace::Nowrap),
    ("pre-wrap", WhiteSpace::PreWrap),
    ("break-spaces", WhiteSpace::BreakSpaces),
    ("pre-line", WhiteSpace::PreLine),
];

const OVERFLOW_WRAPS: &[(&str, OverflowWrap)] = &[
    ("normal", OverflowWrap::Normal),
    ("break-word", OverflowWrap::BreakWord),
    ("anywhere", OverflowWrap::Anywhere),
];

const WORD_BREAKS: &[(&str, WordBreak)] = &[
    ("normal", WordBreak::Normal),
    ("keep-all", WordBreak::KeepAll),
    ("break-all", WordBreak::BreakAll),
    ("break-word", WordBreak::BreakWord),
];

/// CSS Fonts 4 §2.4†, `font-size`: "an absolute length", from the parent's font size
/// `parent` (for `em`, `ex`, percentages and the relative keywords) and the root's `rem`.
/// `<relative-size>`: "a value relative to the computed font-size of the parent ... the
/// user agent may use ... a ratio"; the ratio is 1.2 (CSS 2.1's suggestion, which engines
/// use).
pub fn font_size(v: &[Component], parent: i32, rem: i32) -> Option<i32> {
    match v {
        [Component::Keyword("larger")] => Some(scale(parent, 6, 5)),
        [Component::Keyword("smaller")] => Some(scale(parent, 5, 6)),
        [Component::Keyword(k)] => find(ABSOLUTE_SIZES, k).map(|px| px.saturating_mul(64)),
        [Component::Length(l)] => Some(to_px64(*l, parent, rem).max(0)),
        [Component::Percentage(p)] => Some(percentage_px64(*p, parent).max(0)),
        _ => None,
    }
}

/// CSS Fonts 4 §2.2†, `font-weight`: `normal` is 400, `bold` 700, and §2.2.1's table for
/// `bolder` and `lighter` from the inherited weight `w`.
pub fn font_weight(v: &[Component], w: Num) -> Option<Num> {
    // The weights of the table, all at most 1000, so `n * SCALE` is exact (what
    // `Num::from_int` gives, without its clamp).
    let at = |n: i64| Num {
        millionths: n.saturating_mul(SCALE),
        is_integer: true,
    };
    let lt = |n: i64| w.millionths < n.saturating_mul(SCALE);
    match v {
        [Component::Keyword("normal")] => Some(at(400)),
        [Component::Keyword("bold")] => Some(at(700)),
        // "w < 100: 400; 100 ≤ w < 350: 400; 350 ≤ w < 550: 700; 550 ≤ w < 750: 900;
        // 750 ≤ w < 900: 900; 900 ≤ w: No change".
        [Component::Keyword("bolder")] => Some(if lt(350) {
            at(400)
        } else if lt(550) {
            at(700)
        } else if lt(900) {
            at(900)
        } else {
            w
        }),
        // "w < 100: No change; 100 ≤ w < 350: 100; 350 ≤ w < 550: 100; 550 ≤ w < 750: 400;
        // 750 ≤ w < 900: 700; 900 ≤ w: 700".
        [Component::Keyword("lighter")] => Some(if lt(100) {
            w
        } else if lt(550) {
            at(100)
        } else if lt(750) {
            at(400)
        } else {
            at(700)
        }),
        [Component::Number(n)] => Some(*n),
        _ => None,
    }
}

/// The value of one longhand, computed into `s` from its cascaded components `v`. `s`
/// already holds the computed `font-size` and `color`, which the other properties read.
fn compute_value(
    s: &mut ComputedStyle,
    l: Longhand,
    v: &[Component],
    cx: &mut Context<'_>,
) -> Option<()> {
    use Longhand as L;
    let em = s.font_size;
    let rem = cx.root_font_size;
    let first = v.first();
    let side = |l: Longhand| match l {
        L::MarginTop
        | L::PaddingTop
        | L::BorderTopWidth
        | L::BorderTopStyle
        | L::BorderTopColor => 0usize,
        L::MarginRight
        | L::PaddingRight
        | L::BorderRightWidth
        | L::BorderRightStyle
        | L::BorderRightColor => 1,
        L::MarginBottom
        | L::PaddingBottom
        | L::BorderBottomWidth
        | L::BorderBottomStyle
        | L::BorderBottomColor => 2,
        _ => 3,
    };
    match l {
        // `font-size` and `color` are computed before this is called.
        L::FontSize | L::Color => {}
        L::BackgroundColor => s.background_color = color(v, s.color)?,
        L::TextDecorationColor => s.text_decoration_color = color(v, s.color)?,
        L::BorderTopColor | L::BorderRightColor | L::BorderBottomColor | L::BorderLeftColor => {
            let c = color(v, s.color)?;
            *s.border_color.get_mut(side(l))? = c;
        }
        L::MarginTop | L::MarginRight | L::MarginBottom | L::MarginLeft => {
            let m = if keyword(v) == Some("auto") {
                Size::Auto
            } else {
                Size::Lp(lp(first?, em, rem)?)
            };
            *s.margin.get_mut(side(l))? = m;
        }
        L::PaddingTop | L::PaddingRight | L::PaddingBottom | L::PaddingLeft => {
            *s.padding.get_mut(side(l))? = lp(first?, em, rem)?;
        }
        L::BorderTopWidth | L::BorderRightWidth | L::BorderBottomWidth | L::BorderLeftWidth => {
            // CSS Backgrounds 3 §3.3†: "thin, medium, thick ... The thin keyword is
            // equivalent to 1px, medium to 3px, thick to 5px".
            let w = match keyword(v) {
                Some("thin") => 64,
                Some("medium") => 192,
                Some("thick") => 320,
                _ => length(first?, em, rem)?,
            };
            *s.border_width.get_mut(side(l))? = snap_border_width(w);
        }
        L::BorderTopStyle | L::BorderRightStyle | L::BorderBottomStyle | L::BorderLeftStyle => {
            *s.border_style.get_mut(side(l))? = find(LINE_STYLES, keyword(v)?)?;
        }
        L::Width | L::Height | L::MinWidth | L::MinHeight => {
            let size = if keyword(v) == Some("auto") {
                Size::Auto
            } else {
                Size::Lp(lp(first?, em, rem)?)
            };
            match l {
                L::Width => s.width = size,
                L::Height => s.height = size,
                L::MinWidth => s.min_width = size,
                _ => s.min_height = size,
            }
        }
        L::MaxWidth | L::MaxHeight => {
            let size = if keyword(v) == Some("none") {
                MaxSize::None
            } else {
                MaxSize::Lp(lp(first?, em, rem)?)
            };
            if l == L::MaxWidth {
                s.max_width = size;
            } else {
                s.max_height = size;
            }
        }
        L::Display => s.display = find(DISPLAYS, keyword(v)?)?,
        L::OverflowX => s.overflow_x = find(OVERFLOWS, keyword(v)?)?,
        L::OverflowY => s.overflow_y = find(OVERFLOWS, keyword(v)?)?,
        L::Visibility => s.visibility = find(VISIBILITIES, keyword(v)?)?,
        L::FontFamily => {
            let mut list = Vec::new();
            for c in v {
                match c {
                    Component::FamilyName(n) => list.push(Family::Name(n.clone())),
                    Component::Keyword(k) => list.push(Family::Generic(k)),
                    Component::Comma => {}
                    _ => return None,
                }
            }
            s.font_family = intern(cx.families, list);
        }
        L::FontWeight => s.font_weight = font_weight(v, cx.parent.font_weight)?,
        L::FontStyle => {
            s.font_style = match v {
                [Component::Keyword("normal")] => FontStyle::Normal,
                [Component::Keyword("italic")] => FontStyle::Italic,
                // CSS Fonts 4 §2.3†: "oblique ... If no angle is specified, an angle of 14
                // degrees is used."
                [Component::Keyword("oblique")] => FontStyle::Oblique(SCALE.saturating_mul(14)),
                [Component::Keyword("oblique"), Component::Angle(a)] => {
                    FontStyle::Oblique(degrees(*a))
                }
                _ => return None,
            };
        }
        L::LineHeight => {
            s.line_height = match v {
                [Component::Keyword("normal")] => LineHeight::Normal,
                [Component::Number(n)] => LineHeight::Number(*n),
                // A percentage of "the element's own font size" (CSS 2.1 §10.8.1), computed
                // to an absolute length.
                [Component::Percentage(p)] => LineHeight::Px64(percentage_px64(*p, em)),
                [c] => LineHeight::Px64(length(c, em, rem)?),
                _ => return None,
            };
        }
        L::VerticalAlign => {
            s.vertical_align = match keyword(v) {
                Some(k) => find(VERTICAL_ALIGNS, k)?,
                None => VerticalAlign::Lp(lp(first?, em, rem)?),
            };
        }
        L::TextAlign => {
            s.text_align = match keyword(v)? {
                // CSS Text 3 §7.1†: "match-parent: This value behaves the same as inherit
                // (computes to its parent's computed value) except that an inherited start
                // or end keyword is interpreted against the parent's direction value and
                // results in a computed value of either left or right." (Every element is
                // left to right.)
                "match-parent" => match cx.parent.text_align {
                    TextAlign::Start => TextAlign::Left,
                    TextAlign::End => TextAlign::Right,
                    other => other,
                },
                k => find(TEXT_ALIGNS, k)?,
            };
        }
        L::TextDecorationLine => {
            let mut d = DecorationLines::default();
            for c in v {
                match c {
                    Component::Keyword("none") => {}
                    Component::Keyword("underline") => d.underline = true,
                    Component::Keyword("overline") => d.overline = true,
                    Component::Keyword("line-through") => d.line_through = true,
                    Component::Keyword("blink") => d.blink = true,
                    _ => return None,
                }
            }
            s.text_decoration_line = d;
        }
        L::TextDecorationStyle => {
            s.text_decoration_style = find(DECORATION_STYLES, keyword(v)?)?;
        }
        L::TextIndent => {
            let mut t = TextIndent {
                length: lp(first?, em, rem)?,
                hanging: false,
                each_line: false,
            };
            for c in v.get(1..).unwrap_or_default() {
                match c {
                    Component::Keyword("hanging") => t.hanging = true,
                    Component::Keyword("each-line") => t.each_line = true,
                    _ => return None,
                }
            }
            s.text_indent = t;
        }
        L::WhiteSpace => s.white_space = find(WHITE_SPACES, keyword(v)?)?,
        L::OverflowWrap => s.overflow_wrap = find(OVERFLOW_WRAPS, keyword(v)?)?,
        L::WordBreak => s.word_break = find(WORD_BREAKS, keyword(v)?)?,
        L::BorderSpacing => {
            // CSS 2.1 §17.6.1: "If one length is specified, it gives both the horizontal
            // and vertical spacing."
            let h = length(first?, em, rem)?;
            let w = match v.get(1) {
                Some(c) => length(c, em, rem)?,
                None => h,
            };
            s.border_spacing = [h, w];
        }
        L::BorderCollapse => s.border_collapse = keyword(v)? == "collapse",
        L::TableLayout => s.table_layout_fixed = keyword(v)? == "fixed",
        L::ListStyleType => {
            s.list_style_type = match v {
                [Component::Keyword("none")] => ListStyleType::None,
                [Component::Keyword(k)] => ListStyleType::Named(k),
                [Component::Ident(n)] => ListStyleType::Custom(n.clone()),
                [Component::String(t)] => ListStyleType::String(t.clone()),
                _ => return None,
            };
        }
        // "Parsed, no effect": cascaded and dropped.
        L::BackgroundImage
        | L::BackgroundRepeat
        | L::BackgroundAttachment
        | L::BackgroundPosition
        | L::BackgroundSize
        | L::BackgroundOrigin
        | L::BackgroundClip
        | L::FontVariantCaps
        | L::FontStretch
        | L::TextDecorationThickness
        | L::Cursor
        | L::PointerEvents
        | L::Resize
        | L::Transform
        | L::PageBreakBefore
        | L::TextOverflow => {}
    }
    Some(())
}

/// The index of `list` in `families`, added if new.
fn intern(families: &mut Vec<Vec<Family>>, list: Vec<Family>) -> usize {
    if let Some(i) = families.iter().position(|f| *f == list) {
        return i;
    }
    families.push(list);
    families.len().saturating_sub(1)
}

/// Copy side `i` of `b` into `a`.
fn side<T: Copy>(a: &mut [T; 4], b: &[T; 4], i: usize) {
    if let (Some(x), Some(y)) = (a.get_mut(i), b.get(i)) {
        *x = *y;
    }
}

/// Copy property `l`'s computed value from `from` into `s` (inheriting it, or setting it to
/// its initial value when `from` is the initial style).
fn copy(s: &mut ComputedStyle, from: &ComputedStyle, l: Longhand) {
    use Longhand as L;
    match l {
        L::Color => s.color = from.color,
        L::BackgroundColor => s.background_color = from.background_color,
        L::MarginTop => side(&mut s.margin, &from.margin, 0),
        L::MarginRight => side(&mut s.margin, &from.margin, 1),
        L::MarginBottom => side(&mut s.margin, &from.margin, 2),
        L::MarginLeft => side(&mut s.margin, &from.margin, 3),
        L::PaddingTop => side(&mut s.padding, &from.padding, 0),
        L::PaddingRight => side(&mut s.padding, &from.padding, 1),
        L::PaddingBottom => side(&mut s.padding, &from.padding, 2),
        L::PaddingLeft => side(&mut s.padding, &from.padding, 3),
        L::BorderTopWidth => side(&mut s.border_width, &from.border_width, 0),
        L::BorderRightWidth => side(&mut s.border_width, &from.border_width, 1),
        L::BorderBottomWidth => side(&mut s.border_width, &from.border_width, 2),
        L::BorderLeftWidth => side(&mut s.border_width, &from.border_width, 3),
        L::BorderTopStyle => side(&mut s.border_style, &from.border_style, 0),
        L::BorderRightStyle => side(&mut s.border_style, &from.border_style, 1),
        L::BorderBottomStyle => side(&mut s.border_style, &from.border_style, 2),
        L::BorderLeftStyle => side(&mut s.border_style, &from.border_style, 3),
        L::BorderTopColor => side(&mut s.border_color, &from.border_color, 0),
        L::BorderRightColor => side(&mut s.border_color, &from.border_color, 1),
        L::BorderBottomColor => side(&mut s.border_color, &from.border_color, 2),
        L::BorderLeftColor => side(&mut s.border_color, &from.border_color, 3),
        L::Width => s.width = from.width,
        L::Height => s.height = from.height,
        L::MinWidth => s.min_width = from.min_width,
        L::MinHeight => s.min_height = from.min_height,
        L::MaxWidth => s.max_width = from.max_width,
        L::MaxHeight => s.max_height = from.max_height,
        L::Display => s.display = from.display,
        L::OverflowX => s.overflow_x = from.overflow_x,
        L::OverflowY => s.overflow_y = from.overflow_y,
        L::Visibility => s.visibility = from.visibility,
        L::FontFamily => s.font_family = from.font_family,
        L::FontSize => s.font_size = from.font_size,
        L::FontWeight => s.font_weight = from.font_weight,
        L::FontStyle => s.font_style = from.font_style,
        L::LineHeight => s.line_height = from.line_height,
        L::VerticalAlign => s.vertical_align = from.vertical_align,
        L::TextAlign => s.text_align = from.text_align,
        L::TextDecorationLine => s.text_decoration_line = from.text_decoration_line,
        L::TextDecorationStyle => s.text_decoration_style = from.text_decoration_style,
        L::TextDecorationColor => s.text_decoration_color = from.text_decoration_color,
        L::TextIndent => s.text_indent = from.text_indent,
        L::WhiteSpace => s.white_space = from.white_space,
        L::OverflowWrap => s.overflow_wrap = from.overflow_wrap,
        L::WordBreak => s.word_break = from.word_break,
        L::BorderSpacing => s.border_spacing = from.border_spacing,
        L::BorderCollapse => s.border_collapse = from.border_collapse,
        L::TableLayout => s.table_layout_fixed = from.table_layout_fixed,
        L::ListStyleType => s.list_style_type = from.list_style_type.clone(),
        L::BackgroundImage
        | L::BackgroundRepeat
        | L::BackgroundAttachment
        | L::BackgroundPosition
        | L::BackgroundSize
        | L::BackgroundOrigin
        | L::BackgroundClip
        | L::FontVariantCaps
        | L::FontStretch
        | L::TextDecorationThickness
        | L::Cursor
        | L::PointerEvents
        | L::Resize
        | L::Transform
        | L::PageBreakBefore
        | L::TextOverflow => {}
    }
}

/// The initial style, with `currentcolor`'s initial values resolved against `color`: the
/// border colours and `text-decoration-color` (CSS Backgrounds 3 §3.1†, CSS Text Decoration
/// 3 §2.3†: "Initial: currentcolor"); and the border widths at their initial `medium`, 3px,
/// before the rule that makes them zero for a style of `none` (applied last, in
/// [`compute`]), so that an element whose `border-style` is set gets `medium` borders.
fn initial_with(color: Rgba) -> ComputedStyle {
    let mut s = ComputedStyle::initial();
    s.border_width = [192; 4];
    s.border_color = [color; 4];
    s.text_decoration_color = color;
    s
}

/// One element's computed style, from the cascaded value of each longhand (`cascaded`,
/// indexed by [`index`]: `None` if the cascade gave no value).
pub fn compute(cascaded: &[Option<&Specified>], cx: &mut Context<'_>) -> ComputedStyle {
    let parent = cx.parent;
    let value = |l: Longhand| cascaded.get(index(l)).copied().flatten();
    // §4.3 and §7.3: what a property with no value, or a CSS-wide keyword, gives. `true`
    // means the inherited value.
    let defaulted = |l: Longhand| match value(l) {
        None | Some(Specified::Wide(Wide::Unset | Wide::Revert | Wide::RevertLayer)) => {
            Some(inherited(l))
        }
        Some(Specified::Wide(Wide::Inherit)) => Some(true),
        Some(Specified::Wide(Wide::Initial)) => Some(false),
        Some(Specified::Value(_)) => None,
    };
    let initial = ComputedStyle::initial();
    let mut s = ComputedStyle::initial();
    // `font-size` first: its `em`, `ex` and percentages refer to the parent's.
    let root_initial = MEDIUM_PX64;
    let rem = if cx.is_root {
        root_initial
    } else {
        cx.root_font_size
    };
    s.font_size = match defaulted(Longhand::FontSize) {
        Some(true) => parent.font_size,
        Some(false) => initial.font_size,
        None => match value(Longhand::FontSize) {
            Some(Specified::Value(v)) => {
                font_size(v, parent.font_size, rem).unwrap_or(parent.font_size)
            }
            _ => parent.font_size,
        },
    };
    // `color` next. CSS Color 4 §4.4†: "If currentcolor is the specified value of the
    // color property, it is treated as if the specified value was inherit."
    s.color = match defaulted(Longhand::Color) {
        Some(true) => parent.color,
        Some(false) => BLACK,
        None => match value(Longhand::Color) {
            Some(Specified::Value(v)) => color(v, parent.color).unwrap_or(parent.color),
            _ => parent.color,
        },
    };
    let base = initial_with(s.color);
    let mut cx2 = Context {
        parent,
        root_font_size: rem,
        is_root: cx.is_root,
        families: cx.families,
    };
    for &(_, l) in LONGHANDS {
        if matches!(l, Longhand::FontSize | Longhand::Color) {
            continue;
        }
        match defaulted(l) {
            Some(true) => copy(&mut s, parent, l),
            Some(false) => copy(&mut s, &base, l),
            None => {
                copy(&mut s, &base, l);
                if let Some(Specified::Value(v)) = value(l) {
                    // A value this cannot read leaves the property defaulted.
                    if compute_value(&mut s, l, v, &mut cx2).is_none() {
                        let from = if inherited(l) { parent } else { &base };
                        copy(&mut s, from, l);
                    }
                }
            }
        }
    }
    // CSS Backgrounds 3 §3.3†: border widths are "zero if the border style is none or
    // hidden".
    for (w, st) in s.border_width.iter_mut().zip(s.border_style) {
        if matches!(st, LineStyle::None | LineStyle::Hidden) {
            *w = 0;
        }
    }
    // CSS Overflow 3 §3.1†: "as specified, except with visible/clip computing to auto/hidden
    // (respectively) if one of overflow-x or overflow-y is neither visible nor clip."
    let scrolls = |o: Overflow| !matches!(o, Overflow::Visible | Overflow::Clip);
    if scrolls(s.overflow_x) || scrolls(s.overflow_y) {
        let fix = |o: Overflow| match o {
            Overflow::Visible => Overflow::Auto,
            Overflow::Clip => Overflow::Hidden,
            other => other,
        };
        s.overflow_x = fix(s.overflow_x);
        s.overflow_y = fix(s.overflow_y);
    }
    // CSS Display 3 §2.7†: "The root element's display type is always blockified."
    // Blockification: "If a layout-internal or inline-level box is blockified, its inner
    // display type converts to flow so that it becomes a block container" (an inline-level
    // `inline-table` becomes `table`, §2.7's "except that inline-table becomes table").
    if cx.is_root {
        s.display = match s.display {
            Display::None => Display::None,
            Display::ListItem => Display::ListItem,
            Display::Table | Display::InlineTable => Display::Table,
            _ => Display::Block,
        };
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::number::{Length, LengthUnit};

    fn n(v: i64) -> Num {
        Num::from_int(v)
    }

    fn len(v: i64, unit: LengthUnit) -> Component {
        Component::Length(Length { value: n(v), unit })
    }

    #[test]
    fn font_sizes() {
        let p = 20 * 64;
        let r = 10 * 64;
        assert_eq!(font_size(&[Component::Keyword("x-small")], p, r), Some(640));
        assert_eq!(
            font_size(&[Component::Keyword("larger")], p, r),
            Some(24 * 64)
        );
        assert_eq!(
            font_size(&[Component::Keyword("smaller")], 12 * 64, r),
            Some(640)
        );
        assert_eq!(font_size(&[len(2, LengthUnit::Em)], p, r), Some(40 * 64));
        assert_eq!(font_size(&[len(2, LengthUnit::Rem)], p, r), Some(20 * 64));
        assert_eq!(font_size(&[len(9, LengthUnit::Pt)], p, r), Some(12 * 64));
        assert_eq!(
            font_size(&[Component::Percentage(n(50))], p, r),
            Some(10 * 64)
        );
    }

    #[test]
    fn font_weights() {
        let w = |k: &'static str, from: i64| {
            font_weight(&[Component::Keyword(k)], n(from)).map(|x| x.millionths / SCALE)
        };
        assert_eq!(w("bolder", 400), Some(700));
        assert_eq!(w("bolder", 700), Some(900));
        assert_eq!(w("bolder", 950), Some(950));
        assert_eq!(w("lighter", 400), Some(100));
        assert_eq!(w("lighter", 50), Some(50));
        assert_eq!(w("lighter", 800), Some(700));
    }

    #[test]
    fn border_width_snapping() {
        assert_eq!(snap_border_width(0), 0);
        assert_eq!(snap_border_width(1), 64);
        assert_eq!(snap_border_width(64), 64);
        assert_eq!(snap_border_width(100), 64);
        assert_eq!(snap_border_width(-5), 0);
    }

    fn style(decls: &[(Longhand, Specified)], parent: &ComputedStyle, root: bool) -> ComputedStyle {
        let mut cascaded: Vec<Option<&Specified>> = vec![None; LONGHAND_COUNT];
        for (l, v) in decls {
            if let Some(slot) = cascaded.get_mut(index(*l)) {
                *slot = Some(v);
            }
        }
        let mut families = vec![vec![Family::Generic("serif")]];
        let mut cx = Context {
            parent,
            root_font_size: MEDIUM_PX64,
            is_root: root,
            families: &mut families,
        };
        compute(&cascaded, &mut cx)
    }

    #[test]
    fn defaulting_and_dependencies() {
        let v = |c: Component| Specified::Value(vec![c]);
        let parent = style(
            &[
                (
                    Longhand::Color,
                    v(Component::Color(Color::Rgba([1, 2, 3, 255]))),
                ),
                (Longhand::FontSize, v(len(20, LengthUnit::Px))),
                (
                    Longhand::BackgroundColor,
                    v(Component::Color(Color::Rgba([9, 9, 9, 255]))),
                ),
                (Longhand::LineHeight, v(Component::Number(n(2)))),
            ],
            &ComputedStyle::initial(),
            true,
        );
        assert_eq!(parent.display, Display::Block, "the root is blockified");
        let child = style(
            &[
                (Longhand::MarginTop, v(len(1, LengthUnit::Em))),
                (Longhand::FontSize, v(len(2, LengthUnit::Em))),
                (Longhand::BorderTopStyle, v(Component::Keyword("solid"))),
                (Longhand::BackgroundColor, Specified::Wide(Wide::Inherit)),
                (Longhand::Color, Specified::Wide(Wide::Initial)),
                (Longhand::OverflowX, v(Component::Keyword("hidden"))),
            ],
            &parent,
            false,
        );
        assert_eq!(child.font_size, 40 * 64);
        assert_eq!(
            child.margin[0],
            Size::Lp(Lp::Px64(40 * 64)),
            "em is the element's own"
        );
        assert_eq!(
            child.background_color,
            [9, 9, 9, 255],
            "inherit on a non-inherited property"
        );
        assert_eq!(child.color, BLACK);
        assert_eq!(
            child.border_color[0], BLACK,
            "currentcolor is the element's color"
        );
        assert_eq!(
            child.border_width,
            [3 * 64, 0, 0, 0],
            "medium; none is zero"
        );
        assert_eq!(
            child.line_height,
            LineHeight::Number(n(2)),
            "a number inherits as a number"
        );
        assert_eq!(
            (child.overflow_x, child.overflow_y),
            (Overflow::Hidden, Overflow::Auto)
        );
        assert_eq!(child.display, Display::Inline);
        let grandchild = style(
            &[
                (Longhand::Color, v(Component::Color(Color::CurrentColor))),
                (Longhand::TextAlign, v(Component::Keyword("match-parent"))),
            ],
            &child,
            false,
        );
        assert_eq!(grandchild.color, BLACK);
        assert_eq!(grandchild.text_align, TextAlign::Left);
    }
}
