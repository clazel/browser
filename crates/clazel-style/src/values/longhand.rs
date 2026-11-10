//! The longhands of the subset and their grammars, each cited to the specification that
//! defines the property. Every grammar reads from a [`Cursor`] and returns the value's
//! components in the order CSSOM serializes them; [`super::parse`] requires that it reads
//! every item.

use super::color::{Color, parse_color};
use super::component::Component;
use super::grammar::{
    Range, angle, attempt, custom_ident, keyword, length, length_percentage, number, string, url,
};
use super::items::{Cursor, Item, eq_ignore_case};
use super::number::{Length, LengthUnit, Num, SCALE, degrees};

macro_rules! longhands {
    ($($(#[$doc:meta])* $variant:ident = $name:literal,)*) => {
        /// A longhand property of the subset.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[cfg_attr(kani, derive(kani::Arbitrary))]
        pub enum Longhand {
            $($(#[$doc])* #[doc = concat!("`", $name, "`.")] $variant,)*
        }

        /// Every longhand, with its name.
        pub const LONGHANDS: &[(&str, Longhand)] = &[$(($name, Longhand::$variant),)*];
    };
}

longhands! {
    Color = "color",
    BackgroundColor = "background-color",
    BackgroundImage = "background-image",
    BackgroundRepeat = "background-repeat",
    BackgroundAttachment = "background-attachment",
    BackgroundPosition = "background-position",
    BackgroundSize = "background-size",
    BackgroundOrigin = "background-origin",
    BackgroundClip = "background-clip",
    MarginTop = "margin-top",
    MarginRight = "margin-right",
    MarginBottom = "margin-bottom",
    MarginLeft = "margin-left",
    PaddingTop = "padding-top",
    PaddingRight = "padding-right",
    PaddingBottom = "padding-bottom",
    PaddingLeft = "padding-left",
    BorderTopWidth = "border-top-width",
    BorderRightWidth = "border-right-width",
    BorderBottomWidth = "border-bottom-width",
    BorderLeftWidth = "border-left-width",
    BorderTopStyle = "border-top-style",
    BorderRightStyle = "border-right-style",
    BorderBottomStyle = "border-bottom-style",
    BorderLeftStyle = "border-left-style",
    BorderTopColor = "border-top-color",
    BorderRightColor = "border-right-color",
    BorderBottomColor = "border-bottom-color",
    BorderLeftColor = "border-left-color",
    Width = "width",
    Height = "height",
    MinWidth = "min-width",
    MinHeight = "min-height",
    MaxWidth = "max-width",
    MaxHeight = "max-height",
    Display = "display",
    OverflowX = "overflow-x",
    OverflowY = "overflow-y",
    Visibility = "visibility",
    FontFamily = "font-family",
    FontSize = "font-size",
    FontWeight = "font-weight",
    FontStyle = "font-style",
    FontVariantCaps = "font-variant-caps",
    FontStretch = "font-stretch",
    LineHeight = "line-height",
    VerticalAlign = "vertical-align",
    TextAlign = "text-align",
    TextDecorationLine = "text-decoration-line",
    TextDecorationStyle = "text-decoration-style",
    TextDecorationColor = "text-decoration-color",
    TextDecorationThickness = "text-decoration-thickness",
    TextIndent = "text-indent",
    WhiteSpace = "white-space",
    OverflowWrap = "overflow-wrap",
    WordBreak = "word-break",
    BorderSpacing = "border-spacing",
    BorderCollapse = "border-collapse",
    TableLayout = "table-layout",
    ListStyleType = "list-style-type",
    Cursor = "cursor",
    PointerEvents = "pointer-events",
    Resize = "resize",
    Transform = "transform",
    PageBreakBefore = "page-break-before",
    TextOverflow = "text-overflow",
}

/// Legacy names that are aliases of a longhand (CSS Text 3 §5.5: `word-wrap` is
/// `overflow-wrap`).
pub const ALIASES: &[(&str, Longhand)] = &[("word-wrap", Longhand::OverflowWrap)];

impl Longhand {
    /// The property's name.
    pub fn name(self) -> &'static str {
        LONGHANDS
            .iter()
            .find(|(_, l)| *l == self)
            .map_or("", |(n, _)| n)
    }

    /// True if the Quirks Mode Standard's unitless length quirk (§3.7†) applies to the
    /// property: its list, restricted to the subset.
    pub fn quirky_length(self) -> bool {
        use Longhand as L;
        matches!(
            self,
            L::BorderSpacing
                | L::BorderTopWidth
                | L::BorderRightWidth
                | L::BorderBottomWidth
                | L::BorderLeftWidth
                | L::FontSize
                | L::Height
                | L::MarginTop
                | L::MarginRight
                | L::MarginBottom
                | L::MarginLeft
                | L::MaxHeight
                | L::MaxWidth
                | L::MinHeight
                | L::MinWidth
                | L::PaddingTop
                | L::PaddingRight
                | L::PaddingBottom
                | L::PaddingLeft
                | L::TextIndent
                | L::VerticalAlign
                | L::Width
                | L::BackgroundPosition
        )
    }

    /// True if the hashless hex colour quirk (§3.6†) applies to the property.
    pub fn quirky_color(self) -> bool {
        use Longhand as L;
        matches!(
            self,
            L::BackgroundColor
                | L::BorderTopColor
                | L::BorderRightColor
                | L::BorderBottomColor
                | L::BorderLeftColor
                | L::Color
        )
    }

    /// The initial value, as a shorthand sets it when a part is omitted.
    pub fn initial(self) -> Vec<Component> {
        use Component as C;
        use Longhand as L;
        let kw = |k| vec![C::Keyword(k)];
        let zero = || {
            C::Length(Length {
                value: Num::ZERO,
                unit: LengthUnit::Px,
            })
        };
        match self {
            L::Color
            | L::BorderTopColor
            | L::BorderRightColor
            | L::BorderBottomColor
            | L::BorderLeftColor
            | L::TextDecorationColor => vec![C::Color(Color::CurrentColor)],
            L::BackgroundColor => vec![C::Color(Color::Transparent)],
            L::BackgroundImage
            | L::Transform
            | L::MaxWidth
            | L::MaxHeight
            | L::TextDecorationLine
            | L::Resize => kw("none"),
            L::BackgroundRepeat => kw("repeat"),
            L::BackgroundAttachment => kw("scroll"),
            L::BackgroundPosition => {
                vec![C::Percentage(Num::ZERO), C::Percentage(Num::ZERO)]
            }
            L::BackgroundSize
            | L::Width
            | L::Height
            | L::MinWidth
            | L::MinHeight
            | L::TextDecorationThickness
            | L::Cursor
            | L::PointerEvents
            | L::PageBreakBefore
            | L::TableLayout => kw("auto"),
            L::BackgroundOrigin => kw("padding-box"),
            L::BackgroundClip => kw("border-box"),
            L::MarginTop
            | L::MarginRight
            | L::MarginBottom
            | L::MarginLeft
            | L::PaddingTop
            | L::PaddingRight
            | L::PaddingBottom
            | L::PaddingLeft
            | L::TextIndent => {
                vec![zero()]
            }
            L::BorderTopWidth | L::BorderRightWidth | L::BorderBottomWidth | L::BorderLeftWidth => {
                kw("medium")
            }
            L::BorderTopStyle | L::BorderRightStyle | L::BorderBottomStyle | L::BorderLeftStyle => {
                kw("none")
            }
            L::Display => kw("inline"),
            L::OverflowX | L::OverflowY | L::Visibility => kw("visible"),
            // The initial font family "depends on user agent"; a generic is the stand-in.
            L::FontFamily => kw("serif"),
            L::FontSize => kw("medium"),
            L::FontWeight
            | L::FontStyle
            | L::FontVariantCaps
            | L::FontStretch
            | L::LineHeight
            | L::WhiteSpace
            | L::OverflowWrap
            | L::WordBreak => kw("normal"),
            L::VerticalAlign => kw("baseline"),
            L::TextAlign => kw("start"),
            L::TextDecorationStyle => kw("solid"),
            L::BorderSpacing => vec![zero()],
            L::BorderCollapse => kw("separate"),
            L::ListStyleType => kw("disc"),
            L::TextOverflow => kw("clip"),
        }
    }

    /// Read the property's value from `c`, the quirks applying if `quirks` is set and the
    /// property is on their lists. Reads as much as the grammar takes; the caller checks
    /// that nothing is left.
    pub fn parse(self, c: &mut Cursor<'_>, quirks: bool) -> Option<Vec<Component>> {
        let ql = quirks && self.quirky_length();
        let qc = quirks && self.quirky_color();
        parse_longhand(self, c, ql, qc)
    }
}

/// CSS Backgrounds 3 §3.2†: `<line-style>`.
pub const LINE_STYLES: &[&str] = &[
    "none", "hidden", "dotted", "dashed", "solid", "double", "groove", "ridge", "inset", "outset",
];

/// CSS Fonts 4 §2.1.1†: the generic family keywords.
pub const GENERIC_FAMILIES: &[&str] = &[
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
];

/// CSS Fonts 4 §2.4†: `<absolute-size>` and `<relative-size>`.
const FONT_SIZE_KEYWORDS: &[&str] = &[
    "xx-small",
    "x-small",
    "small",
    "medium",
    "large",
    "x-large",
    "xx-large",
    "xxx-large",
    "larger",
    "smaller",
];

/// CSS Fonts 4 §2.5†: `font-stretch` (`font-width`) keywords.
pub const FONT_STRETCH_KEYWORDS: &[&str] = &[
    "normal",
    "ultra-condensed",
    "extra-condensed",
    "condensed",
    "semi-condensed",
    "semi-expanded",
    "expanded",
    "extra-expanded",
    "ultra-expanded",
];

/// CSS Counter Styles 3 §6† and §7†: the predefined counter styles of the subset's lists,
/// which CSSOM serializes in lower case. Any other `<custom-ident>` is kept as written.
const COUNTER_STYLES: &[&str] = &[
    "decimal",
    "decimal-leading-zero",
    "arabic-indic",
    "armenian",
    "upper-armenian",
    "lower-armenian",
    "bengali",
    "cambodian",
    "khmer",
    "cjk-decimal",
    "devanagari",
    "georgian",
    "gujarati",
    "gurmukhi",
    "hebrew",
    "kannada",
    "lao",
    "malayalam",
    "mongolian",
    "myanmar",
    "oriya",
    "persian",
    "lower-roman",
    "upper-roman",
    "tamil",
    "telugu",
    "thai",
    "tibetan",
    "lower-alpha",
    "lower-latin",
    "upper-alpha",
    "upper-latin",
    "lower-greek",
    "hiragana",
    "hiragana-iroha",
    "katakana",
    "katakana-iroha",
    "disc",
    "circle",
    "square",
    "disclosure-open",
    "disclosure-closed",
    "cjk-earthly-branch",
    "cjk-heavenly-stem",
    "japanese-informal",
    "japanese-formal",
    "korean-hangul-formal",
    "korean-hanja-informal",
    "korean-hanja-formal",
    "simp-chinese-informal",
    "simp-chinese-formal",
    "trad-chinese-informal",
    "trad-chinese-formal",
    "ethiopic-numeric",
];

/// CSS UI 4 §5.1†: `<cursor-predefined>`.
const CURSORS: &[&str] = &[
    "auto",
    "default",
    "none",
    "context-menu",
    "help",
    "pointer",
    "progress",
    "wait",
    "cell",
    "crosshair",
    "text",
    "vertical-text",
    "alias",
    "copy",
    "move",
    "no-drop",
    "not-allowed",
    "grab",
    "grabbing",
    "e-resize",
    "n-resize",
    "ne-resize",
    "nw-resize",
    "s-resize",
    "se-resize",
    "sw-resize",
    "w-resize",
    "ew-resize",
    "ns-resize",
    "nesw-resize",
    "nwse-resize",
    "col-resize",
    "row-resize",
    "all-scroll",
    "zoom-in",
    "zoom-out",
];

/// `<line-width>` (CSS Backgrounds 3 §3.3†).
fn line_width(c: &mut Cursor<'_>, ql: bool) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["thin", "medium", "thick"]) {
        return Some(vec![k]);
    }
    length(c, Range::NonNegative, ql).map(|l| vec![Component::Length(l)])
}

/// One component: a keyword of `table`, or a `<length-percentage>` in `range`.
fn keyword_or_lp(
    c: &mut Cursor<'_>,
    table: &[&'static str],
    range: Range,
    ql: bool,
) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, table) {
        return Some(vec![k]);
    }
    length_percentage(c, range, ql).map(|v| vec![v])
}

fn one_keyword(c: &mut Cursor<'_>, table: &[&'static str]) -> Option<Vec<Component>> {
    keyword(c, table).map(|k| vec![k])
}

fn color(c: &mut Cursor<'_>, qc: bool) -> Option<Vec<Component>> {
    parse_color(c, qc).map(|col| vec![Component::Color(col)])
}

/// `font-family` (CSS Fonts 4 §2.1†): `[ <family-name> | <generic-family> ]#`, where
/// `<family-name>` is `<string> | <custom-ident>+`.
fn font_family(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    let mut out = Vec::new();
    loop {
        if let Some(s) = string(c) {
            out.push(Component::FamilyName(s));
        } else {
            let mut words: Vec<Vec<u32>> = Vec::new();
            while let Some(Item::Ident(_)) = c.peek() {
                words.push(c.ident()?.to_vec());
            }
            match words.as_slice() {
                [] => return None,
                [one] => {
                    if let Some(g) = GENERIC_FAMILIES.iter().find(|g| eq_ignore_case(one, g)) {
                        out.push(Component::Keyword(g));
                    } else if super::is_reserved_ident(one) {
                        // A single identifier must be a <custom-ident>.
                        return None;
                    } else {
                        out.push(Component::FamilyName(one.clone()));
                    }
                }
                many => {
                    // "<custom-ident>+": none may be a CSS-wide keyword or `default`, and
                    // CSS Fonts 4 forbids a generic family as the first.
                    let generic_first = many
                        .first()
                        .is_some_and(|w| GENERIC_FAMILIES.iter().any(|g| eq_ignore_case(w, g)));
                    if generic_first || many.iter().any(|w| super::is_reserved_ident(w)) {
                        return None;
                    }
                    let mut name = Vec::new();
                    for (i, w) in many.iter().enumerate() {
                        if i > 0 {
                            name.push(0x20);
                        }
                        name.extend_from_slice(w);
                    }
                    out.push(Component::FamilyName(name));
                }
            }
        }
        if c.at_end() {
            return Some(out);
        }
        if !c.comma() {
            return Some(out);
        }
        out.push(Component::Comma);
    }
}

/// `font-weight` (CSS Fonts 4 §2.2†): `normal | bold | <number [1,1000]> | bolder | lighter`.
pub fn font_weight(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["normal", "bold", "bolder", "lighter"]) {
        return Some(vec![k]);
    }
    attempt(c, |c| {
        let n = number(c, Range::All)?;
        let ok = n.millionths >= SCALE && n.millionths <= SCALE.saturating_mul(1000);
        ok.then(|| vec![Component::Number(n)])
    })
}

/// `font-style` (CSS Fonts 4 §2.3†): `normal | italic | oblique <angle [-90deg,90deg]>?`.
/// `oblique 0deg` is `normal` as specified, which is how the WPT cases expect it to
/// serialize (the text computes it to `normal`; engines already do so when parsing).
pub fn font_style(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["normal", "italic"]) {
        return Some(vec![k]);
    }
    if !c.eat_keyword("oblique") {
        return None;
    }
    let Some(a) = attempt(c, |c| angle(c, false)) else {
        return Some(vec![Component::Keyword("oblique")]);
    };
    let d = degrees(a);
    let ninety = SCALE.saturating_mul(90);
    if d < ninety.saturating_neg() || d > ninety {
        return None;
    }
    if d == 0 {
        return Some(vec![Component::Keyword("normal")]);
    }
    Some(vec![Component::Keyword("oblique"), Component::Angle(a)])
}

/// `font-variant-caps` (CSS Fonts 4 §6.6†).
pub fn font_variant_caps(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    one_keyword(
        c,
        &[
            "normal",
            "small-caps",
            "all-small-caps",
            "petite-caps",
            "all-petite-caps",
            "unicase",
            "titling-caps",
        ],
    )
}

/// `font-stretch` (CSS Fonts 4 §2.5†): a keyword or `<percentage [0,∞]>`.
pub fn font_stretch(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, FONT_STRETCH_KEYWORDS) {
        return Some(vec![k]);
    }
    super::grammar::percentage(c, Range::NonNegative).map(|p| vec![Component::Percentage(p)])
}

/// `font-size` (CSS Fonts 4 §2.4†).
pub fn font_size(c: &mut Cursor<'_>, ql: bool) -> Option<Vec<Component>> {
    keyword_or_lp(c, FONT_SIZE_KEYWORDS, Range::NonNegative, ql)
}

/// `line-height` (CSS Inline 3 §4.2†, CSS 2.1 §10.8.1): `normal | <number [0,∞]> |
/// <length-percentage [0,∞]>`.
pub fn line_height(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["normal"]) {
        return Some(vec![k]);
    }
    if let Some(n) = number(c, Range::NonNegative) {
        return Some(vec![Component::Number(n)]);
    }
    length_percentage(c, Range::NonNegative, false).map(|v| vec![v])
}

/// `text-decoration-line` (CSS Text Decoration 3 §2.1†): `none | [ underline || overline ||
/// line-through || blink ]`, serialized in that order.
pub fn text_decoration_line(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["none"]) {
        return Some(vec![k]);
    }
    const LINES: [&str; 4] = ["underline", "overline", "line-through", "blink"];
    let mut seen = [false; 4];
    while let Some(k) = c.keyword(&LINES) {
        let i = LINES.iter().position(|l| *l == k)?;
        let slot = seen.get_mut(i)?;
        if *slot {
            return None;
        }
        *slot = true;
    }
    let out: Vec<Component> = LINES
        .iter()
        .zip(seen)
        .filter(|(_, s)| *s)
        .map(|(l, _)| Component::Keyword(l))
        .collect();
    if out.is_empty() { None } else { Some(out) }
}

/// `text-indent` (CSS Text 3 §8.1†): `<length-percentage> && hanging? && each-line?`,
/// serialized length first.
fn text_indent(c: &mut Cursor<'_>, ql: bool) -> Option<Vec<Component>> {
    let mut lp = None;
    let mut hanging = false;
    let mut each_line = false;
    loop {
        if !hanging && c.eat_keyword("hanging") {
            hanging = true;
        } else if !each_line && c.eat_keyword("each-line") {
            each_line = true;
        } else if lp.is_none() {
            match length_percentage(c, Range::All, ql) {
                Some(v) => lp = Some(v),
                None => break,
            }
        } else {
            break;
        }
    }
    let mut out = vec![lp?];
    if hanging {
        out.push(Component::Keyword("hanging"));
    }
    if each_line {
        out.push(Component::Keyword("each-line"));
    }
    Some(out)
}

/// `<image>` of the subset (CSS Images 3 §2†): `<url>` or `linear-gradient()` and
/// `repeating-linear-gradient()` (§3.1†).
pub fn image(c: &mut Cursor<'_>) -> Option<Component> {
    if let Some(u) = url(c) {
        return Some(Component::Url(u));
    }
    attempt(c, |c| {
        let (name, args) = c.function()?;
        let name = if eq_ignore_case(name, "linear-gradient") {
            "linear-gradient"
        } else if eq_ignore_case(name, "repeating-linear-gradient") {
            "repeating-linear-gradient"
        } else {
            return None;
        };
        let parts = super::grammar::whole(args, linear_gradient)?;
        Some(Component::Function(name, parts))
    })
}

/// `linear-gradient()`'s arguments (CSS Images 3 §3.1.1†): `[ <angle> | <zero> | to
/// <side-or-corner> ]? , <color-stop-list>`.
fn linear_gradient(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    let mut out = Vec::new();
    if let Some(a) = attempt(c, |c| angle(c, true)) {
        out.push(Component::Angle(a));
        if !c.comma() {
            return None;
        }
        out.push(Component::Comma);
    } else if c.eat_keyword("to") {
        out.push(Component::Keyword("to"));
        let h = keyword(c, &["left", "right"]);
        let v = keyword(c, &["top", "bottom"]);
        let h = if h.is_none() {
            keyword(c, &["left", "right"])
        } else {
            h
        };
        if h.is_none() && v.is_none() {
            return None;
        }
        out.extend(h);
        out.extend(v);
        if !c.comma() {
            return None;
        }
        out.push(Component::Comma);
    }
    // <color-stop-list>: <color> <length-percentage>{0,2} items, with an optional single
    // <length-percentage> hint between two of them; at least two colour stops.
    let mut stops = 0usize;
    let mut last_was_hint = true;
    loop {
        if let Some(col) = parse_color(c, false) {
            out.push(Component::Color(col));
            for _ in 0..2 {
                match length_percentage(c, Range::All, false) {
                    Some(v) => out.push(v),
                    None => break,
                }
            }
            stops = stops.saturating_add(1);
            last_was_hint = false;
        } else if !last_was_hint {
            out.push(length_percentage(c, Range::All, false)?);
            last_was_hint = true;
        } else {
            return None;
        }
        if c.at_end() {
            break;
        }
        if !c.comma() {
            return None;
        }
        out.push(Component::Comma);
    }
    if stops < 2 || last_was_hint {
        return None;
    }
    Some(out)
}

/// `background-image` (CSS Backgrounds 3 §2.3†): `<bg-image>#`, `<bg-image> = none | <image>`.
fn bg_images(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    let mut out = Vec::new();
    loop {
        if let Some(k) = keyword(c, &["none"]) {
            out.push(k);
        } else {
            out.push(image(c)?);
        }
        if c.at_end() || !c.comma() {
            return Some(out);
        }
        out.push(Component::Comma);
    }
}

/// `<repeat-style>` (CSS Backgrounds 3 §2.4†).
pub fn repeat_style(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["repeat-x", "repeat-y"]) {
        return Some(vec![k]);
    }
    const R: &[&str] = &["repeat", "space", "round", "no-repeat"];
    let first = keyword(c, R)?;
    match keyword(c, R) {
        Some(second) if second != first => Some(vec![first, second]),
        _ => Some(vec![first]),
    }
}

/// `<bg-position>` of one or two values (CSS Backgrounds 3 §2.6†); the three- and
/// four-value forms are not in the subset.
pub fn bg_position(c: &mut Cursor<'_>, ql: bool) -> Option<Vec<Component>> {
    const H: &[&str] = &["left", "right"];
    const V: &[&str] = &["top", "bottom"];
    let one = |c: &mut Cursor<'_>| -> Option<Component> {
        if let Some(k) = keyword(c, &["left", "right", "top", "bottom", "center"]) {
            return Some(k);
        }
        length_percentage(c, Range::All, ql)
    };
    let first = one(c)?;
    let Some(second) = attempt(c, |c| one(c)) else {
        return Some(vec![first]);
    };
    let is = |x: &Component, t: &[&str]| matches!(x, Component::Keyword(k) if t.contains(k));
    let ok = if is(&first, V) || is(&second, H) {
        // A vertical keyword first, or a horizontal one second: both must be keywords.
        matches!(first, Component::Keyword(_))
            && matches!(second, Component::Keyword(_))
            && !(is(&first, V) && is(&second, V))
            && !(is(&first, H) && is(&second, H))
    } else {
        true
    };
    ok.then(|| vec![first, second])
}

/// `<bg-size>` (CSS Backgrounds 3 §3.9†).
pub fn bg_size(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["cover", "contain"]) {
        return Some(vec![k]);
    }
    let one = |c: &mut Cursor<'_>| -> Option<Component> {
        if let Some(k) = keyword(c, &["auto"]) {
            return Some(k);
        }
        length_percentage(c, Range::NonNegative, false)
    };
    let first = one(c)?;
    match attempt(c, |c| one(c)) {
        Some(second) => Some(vec![first, second]),
        None => Some(vec![first]),
    }
}

/// `<visual-box>` (CSS Box 4 §3†).
pub const VISUAL_BOXES: &[&str] = &["border-box", "padding-box", "content-box"];

/// A comma-separated list of `f`.
fn list_of(
    c: &mut Cursor<'_>,
    f: impl Fn(&mut Cursor<'_>) -> Option<Vec<Component>>,
) -> Option<Vec<Component>> {
    let mut out = f(c)?;
    while !c.at_end() && c.comma() {
        out.push(Component::Comma);
        out.extend(f(c)?);
    }
    Some(out)
}

/// `cursor` (CSS UI 4 §5.1†): `[ <url> [ <x> <y> ]? , ]* <cursor-predefined>`. `image-set()`
/// is not in the subset.
fn cursor(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    let mut out = Vec::new();
    while let Some(u) = url(c) {
        out.push(Component::Url(u));
        if let Some(x) = number(c, Range::All) {
            out.push(Component::Number(x));
            out.push(Component::Number(number(c, Range::All)?));
        }
        if !c.comma() {
            return None;
        }
        out.push(Component::Comma);
    }
    out.push(keyword(c, CURSORS)?);
    Some(out)
}

/// `transform` (CSS Transforms 1 §7†): `none | <transform-function>+`, with the 2D
/// functions of §12†.
fn transform(c: &mut Cursor<'_>) -> Option<Vec<Component>> {
    if let Some(k) = keyword(c, &["none"]) {
        return Some(vec![k]);
    }
    let mut out = Vec::new();
    while let Some(Item::Function { .. }) = c.peek() {
        out.push(transform_function(c)?);
    }
    if out.is_empty() { None } else { Some(out) }
}

/// The 2D transform functions (§12†) and the counts and types of their arguments.
const TRANSFORM_FUNCTIONS: &[(&str, ArgKind, usize, usize)] = &[
    ("matrix", ArgKind::Number, 6, 6),
    ("translate", ArgKind::LengthPercentage, 1, 2),
    ("translatex", ArgKind::LengthPercentage, 1, 1),
    ("translatey", ArgKind::LengthPercentage, 1, 1),
    ("scale", ArgKind::Number, 1, 2),
    ("scalex", ArgKind::Number, 1, 1),
    ("scaley", ArgKind::Number, 1, 1),
    ("rotate", ArgKind::Angle, 1, 1),
    ("skew", ArgKind::Angle, 1, 2),
    ("skewx", ArgKind::Angle, 1, 1),
    ("skewy", ArgKind::Angle, 1, 1),
];

/// The serialized names of [`TRANSFORM_FUNCTIONS`], in the same order.
const TRANSFORM_NAMES: &[&str] = &[
    "matrix",
    "translate",
    "translateX",
    "translateY",
    "scale",
    "scaleX",
    "scaleY",
    "rotate",
    "skew",
    "skewX",
    "skewY",
];

#[derive(Clone, Copy)]
enum ArgKind {
    Number,
    LengthPercentage,
    Angle,
}

fn transform_function(c: &mut Cursor<'_>) -> Option<Component> {
    let (name, mut args) = c.function()?;
    let i = TRANSFORM_FUNCTIONS
        .iter()
        .position(|(n, _, _, _)| eq_ignore_case(name, n))?;
    let (_, kind, min, max) = TRANSFORM_FUNCTIONS.get(i).copied()?;
    let display = TRANSFORM_NAMES.get(i).copied()?;
    let mut out = Vec::new();
    let mut n = 0usize;
    loop {
        let v = match kind {
            ArgKind::Number => number(&mut args, Range::All).map(Component::Number),
            ArgKind::LengthPercentage => length_percentage(&mut args, Range::All, false),
            ArgKind::Angle => angle(&mut args, true).map(Component::Angle),
        }?;
        out.push(v);
        n = n.saturating_add(1);
        if args.at_end() {
            break;
        }
        if n >= max || !args.comma() {
            return None;
        }
        out.push(Component::Comma);
    }
    (n >= min).then_some(Component::Function(display, out))
}

/// `display` (CSS Display 3 §2†), its single keywords in the subset (phase-5.md item 5.6):
/// `none`, `block`, `inline`, `inline-block`, `list-item` and the table values.
const DISPLAYS: &[&str] = &[
    "none",
    "block",
    "inline",
    "inline-block",
    "list-item",
    "table",
    "inline-table",
    "table-row-group",
    "table-header-group",
    "table-footer-group",
    "table-row",
    "table-cell",
    "table-column-group",
    "table-column",
    "table-caption",
];

/// The grammar of each longhand.
fn parse_longhand(l: Longhand, c: &mut Cursor<'_>, ql: bool, qc: bool) -> Option<Vec<Component>> {
    use Longhand as L;
    match l {
        // CSS Color 4 §3.1†: `color: <color>`.
        L::Color => color(c, qc),
        // CSS Backgrounds 3 §2.1†, §3.1†, CSS Text Decoration 3 §2.3†.
        L::BackgroundColor
        | L::BorderTopColor
        | L::BorderRightColor
        | L::BorderBottomColor
        | L::BorderLeftColor
        | L::TextDecorationColor => color(c, qc),
        L::BackgroundImage => bg_images(c),
        L::BackgroundRepeat => list_of(c, repeat_style),
        // CSS Backgrounds 3 §2.5†.
        L::BackgroundAttachment => list_of(c, |c| one_keyword(c, &["scroll", "fixed", "local"])),
        L::BackgroundPosition => list_of(c, |c| bg_position(c, ql)),
        L::BackgroundSize => list_of(c, bg_size),
        // CSS Backgrounds 3 §2.7† and §2.8†.
        L::BackgroundOrigin | L::BackgroundClip => list_of(c, |c| one_keyword(c, VISUAL_BOXES)),
        // CSS Box 3 §5.1†: `<length-percentage> | auto`.
        L::MarginTop | L::MarginRight | L::MarginBottom | L::MarginLeft => {
            keyword_or_lp(c, &["auto"], Range::All, ql)
        }
        // CSS Box 3 §6.1†: `<length-percentage [0,∞]>`.
        L::PaddingTop | L::PaddingRight | L::PaddingBottom | L::PaddingLeft => {
            length_percentage(c, Range::NonNegative, ql).map(|v| vec![v])
        }
        L::BorderTopWidth | L::BorderRightWidth | L::BorderBottomWidth | L::BorderLeftWidth => {
            line_width(c, ql)
        }
        L::BorderTopStyle | L::BorderRightStyle | L::BorderBottomStyle | L::BorderLeftStyle => {
            one_keyword(c, LINE_STYLES)
        }
        // CSS Sizing 3 §3.1† and §3.2†: `auto | <length-percentage [0,∞]>` (the intrinsic
        // keywords are not in the subset), `max-*`: `none | …`.
        L::Width | L::Height | L::MinWidth | L::MinHeight => {
            keyword_or_lp(c, &["auto"], Range::NonNegative, ql)
        }
        L::MaxWidth | L::MaxHeight => keyword_or_lp(c, &["none"], Range::NonNegative, ql),
        L::Display => one_keyword(c, DISPLAYS),
        // CSS Overflow 3 §3.1†.
        L::OverflowX | L::OverflowY => {
            one_keyword(c, &["visible", "hidden", "clip", "scroll", "auto"])
        }
        // CSS 2.1 §11.2.
        L::Visibility => one_keyword(c, &["visible", "hidden", "collapse"]),
        L::FontFamily => font_family(c),
        L::FontSize => font_size(c, ql),
        L::FontWeight => font_weight(c),
        L::FontStyle => font_style(c),
        L::FontVariantCaps => font_variant_caps(c),
        L::FontStretch => font_stretch(c),
        L::LineHeight => line_height(c),
        // CSS 2.1 §10.8.1.
        L::VerticalAlign => keyword_or_lp(
            c,
            &[
                "baseline",
                "sub",
                "super",
                "top",
                "text-top",
                "middle",
                "bottom",
                "text-bottom",
            ],
            Range::All,
            ql,
        ),
        // CSS Text 3 §7.1†.
        L::TextAlign => one_keyword(
            c,
            &[
                "start",
                "end",
                "left",
                "right",
                "center",
                "justify",
                "match-parent",
                "justify-all",
            ],
        ),
        L::TextDecorationLine => text_decoration_line(c),
        // CSS Text Decoration 3 §2.2†.
        L::TextDecorationStyle => one_keyword(c, &["solid", "double", "dotted", "dashed", "wavy"]),
        // CSS Text Decoration 4 §2.4†: `auto | from-font | <length-percentage>`.
        L::TextDecorationThickness => keyword_or_lp(c, &["auto", "from-font"], Range::All, false),
        L::TextIndent => text_indent(c, ql),
        // CSS Text 3 §3†.
        L::WhiteSpace => one_keyword(
            c,
            &[
                "normal",
                "pre",
                "nowrap",
                "pre-wrap",
                "break-spaces",
                "pre-line",
            ],
        ),
        // CSS Text 3 §5.5†.
        L::OverflowWrap => one_keyword(c, &["normal", "break-word", "anywhere"]),
        // CSS Text 3 §5.2†.
        L::WordBreak => one_keyword(c, &["normal", "keep-all", "break-all", "break-word"]),
        // CSS 2.1 §17.6.1: `<length> <length>?`, not negative.
        L::BorderSpacing => {
            let a = length(c, Range::NonNegative, ql)?;
            let mut out = vec![Component::Length(a)];
            if let Some(b) = length(c, Range::NonNegative, ql) {
                out.push(Component::Length(b));
            }
            Some(out)
        }
        // CSS 2.1 §17.6.
        L::BorderCollapse => one_keyword(c, &["collapse", "separate"]),
        // CSS 2.1 §17.5.2.
        L::TableLayout => one_keyword(c, &["auto", "fixed"]),
        // CSS Lists 3 §3.3†: `<counter-style> | <string> | none`.
        L::ListStyleType => {
            if let Some(k) = keyword(c, &["none"]).or_else(|| keyword(c, COUNTER_STYLES)) {
                return Some(vec![k]);
            }
            if let Some(s) = string(c) {
                return Some(vec![Component::String(s)]);
            }
            custom_ident(c, &["none"]).map(|s| vec![Component::Ident(s)])
        }
        L::Cursor => cursor(c),
        // CSS UI 4 §6.1† (`pointer-events`, as SVG 2 §16.6† defines it).
        L::PointerEvents => one_keyword(
            c,
            &[
                "auto",
                "none",
                "visiblepainted",
                "visiblefill",
                "visiblestroke",
                "visible",
                "painted",
                "fill",
                "stroke",
                "all",
                "bounding-box",
            ],
        ),
        // CSS UI 4 §5.3†.
        L::Resize => one_keyword(
            c,
            &["none", "both", "horizontal", "vertical", "block", "inline"],
        ),
        L::Transform => transform(c),
        // CSS 2.1 §13.3.1.
        L::PageBreakBefore => one_keyword(c, &["auto", "always", "avoid", "left", "right"]),
        // CSS Overflow 4 §3.1†: `clip | ellipsis | <string>`, one value (the two-value form
        // is not in the subset).
        L::TextOverflow => {
            if let Some(k) = keyword(c, &["clip", "ellipsis"]) {
                return Some(vec![k]);
            }
            string(c).map(|s| vec![Component::String(s)])
        }
    }
}
