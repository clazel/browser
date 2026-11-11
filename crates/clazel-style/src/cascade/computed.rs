//! The output of the cascade: each element's computed values for the properties of the
//! subset that Phase 5 applies, and the per-node table that holds them (phase-5.md item 5.7,
//! "a side table of computed values indexed by node id"; items 5.13 to 5.16 and 5.20 read
//! it).
//!
//! A computed value is CSS Cascade 4 §4.4's: "the result of resolving the specified value as
//! defined in the 'Computed Value' line of the property definition table". Each field's
//! documentation gives that line, from the property's defining specification (the same ones
//! `values/longhand.rs` cites for the grammar). Lengths are 1/64 px in an `i32`, as
//! `values::number::to_px64` gives them; percentages that stay percentages (a computed
//! `<length-percentage>` keeps its percentage, which layout resolves) are a
//! [`Num`](crate::values::number::Num) of percent.
//!
//! The properties the README lists as "parsed, no effect" (`cursor`, `pointer-events`,
//! `resize`, `transform`, `page-break-before`, `text-overflow`, the background images and
//! their positions, sizes, repeats, attachments, origins and clips, `font-variant-caps`,
//! `font-stretch`, `text-decoration-thickness`) are cascaded and dropped: no later item reads
//! them, and Phase 7's `getComputedStyle` will add them here.

use crate::values::number::Num;

/// sRGB red, green, blue and alpha, each 0 to 255: a computed `<color>` (CSS Color 4 §4.6†:
/// "the computed value of a color is ... the resolved color", with `currentcolor` resolved
/// to the element's `color`; see the module's modelling choices in `cascade/mod.rs`).
pub type Rgba = [u8; 4];

/// Opaque black, the initial value of `color` (HTML §15.3.4: "The initial value for the
/// 'color' property is expected to be black").
pub const BLACK: Rgba = [0, 0, 0, 255];
/// `transparent`.
pub const TRANSPARENT: Rgba = [0, 0, 0, 0];

/// A computed `<length-percentage>`: "a percentage, or an absolute length" (CSS Values 4
/// §5.5†).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Lp {
    /// An absolute length in 1/64 px.
    Px64(i32),
    /// A percentage, in percent (50% is 50).
    Percent(Num),
}

/// `auto` or a computed `<length-percentage>` (`margin-*`, `width`, `height`, `min-width`,
/// `min-height`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Size {
    /// `auto`.
    Auto,
    /// A length or a percentage.
    Lp(Lp),
}

/// `none` or a computed `<length-percentage>` (`max-width`, `max-height`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum MaxSize {
    /// `none`.
    None,
    /// A length or a percentage.
    Lp(Lp),
}

/// `<line-style>` (CSS Backgrounds 3 §3.2†). Every style is computed; layout draws them all
/// `solid` (phase-5.md item 5.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum LineStyle {
    /// `none`.
    None,
    /// `hidden`.
    Hidden,
    /// `dotted`.
    Dotted,
    /// `dashed`.
    Dashed,
    /// `solid`.
    Solid,
    /// `double`.
    Double,
    /// `groove`.
    Groove,
    /// `ridge`.
    Ridge,
    /// `inset`.
    Inset,
    /// `outset`.
    Outset,
}

/// `display` (CSS Display 3 §2†), the values of the subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Display {
    /// `none`.
    None,
    /// `block`.
    Block,
    /// `inline`.
    Inline,
    /// `inline-block`.
    InlineBlock,
    /// `list-item`.
    ListItem,
    /// `table`.
    Table,
    /// `inline-table`.
    InlineTable,
    /// `table-row-group`.
    TableRowGroup,
    /// `table-header-group`.
    TableHeaderGroup,
    /// `table-footer-group`.
    TableFooterGroup,
    /// `table-row`.
    TableRow,
    /// `table-cell`.
    TableCell,
    /// `table-column-group`.
    TableColumnGroup,
    /// `table-column`.
    TableColumn,
    /// `table-caption`.
    TableCaption,
}

/// `overflow-x`, `overflow-y` (CSS Overflow 3 §3.1†).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Overflow {
    /// `visible`.
    Visible,
    /// `hidden`.
    Hidden,
    /// `clip`.
    Clip,
    /// `scroll`.
    Scroll,
    /// `auto`.
    Auto,
}

/// `visibility` (CSS 2.1 §11.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Visibility {
    /// `visible`.
    Visible,
    /// `hidden`.
    Hidden,
    /// `collapse`.
    Collapse,
}

/// One entry of a computed `font-family` (CSS Fonts 4 §2.1†: "list, each item a string
/// and/or `<generic-family>` keywords").
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Family {
    /// A family name.
    Name(Vec<u32>),
    /// A generic family keyword, in lower case.
    Generic(&'static str),
}

/// `font-style` (CSS Fonts 4 §2.3†): "the keyword specified, plus angle in degrees if
/// specified".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum FontStyle {
    /// `normal`.
    Normal,
    /// `italic`.
    Italic,
    /// `oblique` with its angle in millionths of a degree (`oblique` alone is 14 degrees,
    /// §2.3†).
    Oblique(i64),
}

/// `line-height` (CSS Inline 3 §4.2†, CSS 2.1 §10.8.1): "for `<length-percentage>` the
/// absolute length, otherwise as specified".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum LineHeight {
    /// `normal`.
    Normal,
    /// A `<number>`, which descendants inherit as a number.
    Number(Num),
    /// An absolute length in 1/64 px.
    Px64(i32),
}

/// `vertical-align` (CSS 2.1 §10.8.1): "for `<percentage>` and `<length>` the absolute
/// length, otherwise as specified". A percentage refers to the element's own used
/// `line-height`, which is layout's, so it is kept as a percentage (as CSS Inline 3† has
/// it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum VerticalAlign {
    /// `baseline`.
    Baseline,
    /// `sub`.
    Sub,
    /// `super`.
    Super,
    /// `top`.
    Top,
    /// `text-top`.
    TextTop,
    /// `middle`.
    Middle,
    /// `bottom`.
    Bottom,
    /// `text-bottom`.
    TextBottom,
    /// A length or a percentage.
    Lp(Lp),
}

/// `text-align` (CSS Text 3 §7.1†): "keyword as specified, except for `match-parent` which
/// computes as defined above". `match-parent` is resolved against the parent (always
/// left-to-right in this phase), so it never appears here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum TextAlign {
    /// `start`.
    Start,
    /// `end`.
    End,
    /// `left`.
    Left,
    /// `right`.
    Right,
    /// `center`.
    Center,
    /// `justify`.
    Justify,
    /// `justify-all`.
    JustifyAll,
}

/// `text-decoration-line` (CSS Text Decoration 3 §2.1†): "as specified".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct DecorationLines {
    /// `underline`.
    pub underline: bool,
    /// `overline`.
    pub overline: bool,
    /// `line-through`.
    pub line_through: bool,
    /// `blink`.
    pub blink: bool,
}

/// `text-decoration-style` (CSS Text Decoration 3 §2.2†).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum DecorationStyle {
    /// `solid`.
    Solid,
    /// `double`.
    Double,
    /// `dotted`.
    Dotted,
    /// `dashed`.
    Dashed,
    /// `wavy`.
    Wavy,
}

/// `text-indent` (CSS Text 3 §8.1†): "computed `<length-percentage>` value, plus any
/// specified keywords".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct TextIndent {
    /// The length or percentage.
    pub length: Lp,
    /// `hanging`.
    pub hanging: bool,
    /// `each-line`.
    pub each_line: bool,
}

/// `white-space` (CSS Text 3 §3†), as the subset parses it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum WhiteSpace {
    /// `normal`.
    Normal,
    /// `pre`.
    Pre,
    /// `nowrap`.
    Nowrap,
    /// `pre-wrap`.
    PreWrap,
    /// `break-spaces`.
    BreakSpaces,
    /// `pre-line`.
    PreLine,
}

/// `overflow-wrap` (CSS Text 3 §5.5†).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum OverflowWrap {
    /// `normal`.
    Normal,
    /// `break-word`.
    BreakWord,
    /// `anywhere`.
    Anywhere,
}

/// `word-break` (CSS Text 3 §5.2†).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum WordBreak {
    /// `normal`.
    Normal,
    /// `keep-all`.
    KeepAll,
    /// `break-all`.
    BreakAll,
    /// `break-word`.
    BreakWord,
}

/// `list-style-type` (CSS Lists 3 §3.3†): "as specified".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ListStyleType {
    /// `none`.
    None,
    /// A predefined counter style, in lower case.
    Named(&'static str),
    /// Any other `<counter-style-name>`, as written (it names no style, so layout uses
    /// `decimal`, CSS Counter Styles 3 §1.2†).
    Custom(Vec<u32>),
    /// A `<string>`.
    String(Vec<u32>),
}

/// How an element of HTML §15.3.3 and §15.3.8 "align[s] descendants" (`center`, and
/// `div`, `thead`, `tbody`, `tfoot`, `tr`, `td` and `th` with an `align` attribute): not a
/// CSS property, so it is given beside the computed values for layout to apply (HTML §15.2
/// "align descendants").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum AlignDescendants {
    /// To the left.
    Left,
    /// To the center.
    Center,
    /// To the right.
    Right,
}

/// One element's computed values for the applied properties of the subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedStyle {
    /// `color` (CSS Color 4 §3.1†): the resolved colour; `currentcolor` is the inherited
    /// value.
    pub color: Rgba,
    /// `background-color` (CSS Backgrounds 3 §2.1†): computed colour.
    pub background_color: Rgba,
    /// `margin-top`, `-right`, `-bottom`, `-left` (CSS Box 3 §5.1†): "the keyword `auto` or
    /// a computed `<length-percentage>` value".
    pub margin: [Size; 4],
    /// `padding-top`, `-right`, `-bottom`, `-left` (CSS Box 3 §6.1†): "a computed
    /// `<length-percentage>` value".
    pub padding: [Lp; 4],
    /// `border-*-width` in 1/64 px (CSS Backgrounds 3 §3.3†): "absolute length, snapped as a
    /// border width; zero if the border style is none or hidden".
    pub border_width: [i32; 4],
    /// `border-*-style` (CSS Backgrounds 3 §3.2†): "specified keyword".
    pub border_style: [LineStyle; 4],
    /// `border-*-color` (CSS Backgrounds 3 §3.1†): "the computed color".
    pub border_color: [Rgba; 4],
    /// `width` (CSS Sizing 3 §3.1†): "as specified, with `<length-percentage>` values
    /// computed".
    pub width: Size,
    /// `height`, likewise.
    pub height: Size,
    /// `min-width` (CSS Sizing 3 §3.2†), likewise.
    pub min_width: Size,
    /// `min-height`, likewise.
    pub min_height: Size,
    /// `max-width` (CSS Sizing 3 §3.3†), likewise.
    pub max_width: MaxSize,
    /// `max-height`, likewise.
    pub max_height: MaxSize,
    /// `display` (CSS Display 3 §2†): "a pair of keywords representing the inner and outer
    /// display types", blockified for the root element (§2.7†).
    pub display: Display,
    /// `overflow-x` (CSS Overflow 3 §3.1†): "as specified, except with `visible`/`clip`
    /// computing to `auto`/`hidden` (respectively) if one of `overflow-x` or `overflow-y`
    /// is neither `visible` nor `clip`".
    pub overflow_x: Overflow,
    /// `overflow-y`, likewise.
    pub overflow_y: Overflow,
    /// `visibility` (CSS 2.1 §11.2): as specified.
    pub visibility: Visibility,
    /// `font-family` (CSS Fonts 4 §2.1†): an index into [`ComputedTable::families`], so that
    /// inheriting a family list copies an index.
    pub font_family: usize,
    /// `font-size` in 1/64 px (CSS Fonts 4 §2.4†): "an absolute length".
    pub font_size: i32,
    /// `font-weight` (CSS Fonts 4 §2.2†): "a number, see below" (1 to 1000).
    pub font_weight: Num,
    /// `font-style`.
    pub font_style: FontStyle,
    /// `line-height`.
    pub line_height: LineHeight,
    /// `vertical-align`.
    pub vertical_align: VerticalAlign,
    /// `text-align`.
    pub text_align: TextAlign,
    /// `text-decoration-line`.
    pub text_decoration_line: DecorationLines,
    /// `text-decoration-style`.
    pub text_decoration_style: DecorationStyle,
    /// `text-decoration-color` (CSS Text Decoration 3 §2.3†): "computed color".
    pub text_decoration_color: Rgba,
    /// `text-indent`.
    pub text_indent: TextIndent,
    /// `white-space`.
    pub white_space: WhiteSpace,
    /// `overflow-wrap`.
    pub overflow_wrap: OverflowWrap,
    /// `word-break`.
    pub word_break: WordBreak,
    /// `border-spacing` in 1/64 px, horizontal then vertical (CSS 2.1 §17.6.1: "two absolute
    /// lengths").
    pub border_spacing: [i32; 2],
    /// `border-collapse` (CSS 2.1 §17.6): true for `collapse`.
    pub border_collapse: bool,
    /// `table-layout` (CSS 2.1 §17.5.2): true for `fixed`.
    pub table_layout_fixed: bool,
    /// `list-style-type`.
    pub list_style_type: ListStyleType,
    /// HTML's "align descendants", if the element does (not a CSS property; never
    /// inherited).
    pub align_descendants: Option<AlignDescendants>,
}

/// `medium`, the initial `font-size`: 16 px (CSS Fonts 4 §2.4.1†'s reference size, as every
/// engine has it), in 1/64 px.
pub const MEDIUM_PX64: i32 = 1024;

/// The index of the initial family list (`serif`) in every [`ComputedTable::families`].
pub const INITIAL_FAMILY: usize = 0;

impl ComputedStyle {
    /// Every property's initial value (CSS Cascade 4 §7.1), as its definition table gives
    /// it, computed (no `em` or percentage is involved): the computed style of an element
    /// whose cascade gives nothing and whose parent is not an element.
    pub fn initial() -> ComputedStyle {
        let zero = Lp::Px64(0);
        ComputedStyle {
            color: BLACK,
            background_color: TRANSPARENT,
            margin: [Size::Lp(zero); 4],
            padding: [zero; 4],
            // `medium`, but zero since the initial style is `none`.
            border_width: [0; 4],
            border_style: [LineStyle::None; 4],
            // `currentcolor`, the initial `color`.
            border_color: [BLACK; 4],
            width: Size::Auto,
            height: Size::Auto,
            min_width: Size::Auto,
            min_height: Size::Auto,
            max_width: MaxSize::None,
            max_height: MaxSize::None,
            display: Display::Inline,
            overflow_x: Overflow::Visible,
            overflow_y: Overflow::Visible,
            visibility: Visibility::Visible,
            font_family: INITIAL_FAMILY,
            font_size: MEDIUM_PX64,
            font_weight: Num::from_int(400),
            font_style: FontStyle::Normal,
            line_height: LineHeight::Normal,
            vertical_align: VerticalAlign::Baseline,
            text_align: TextAlign::Start,
            text_decoration_line: DecorationLines::default(),
            text_decoration_style: DecorationStyle::Solid,
            text_decoration_color: BLACK,
            text_indent: TextIndent {
                length: zero,
                hanging: false,
                each_line: false,
            },
            white_space: WhiteSpace::Normal,
            overflow_wrap: OverflowWrap::Normal,
            word_break: WordBreak::Normal,
            border_spacing: [0, 0],
            border_collapse: false,
            table_layout_fixed: false,
            list_style_type: ListStyleType::Named("disc"),
            align_descendants: None,
        }
    }
}

/// The computed values of a document: one entry per node of its arena, indexed by node id
/// (phase-5.md, "computed style and the layout tree are side tables keyed by node id").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedTable {
    /// `styles[n]` is element `n`'s computed style; `None` for a node that is not an
    /// element, and for an element not in the document tree (in a `template`'s contents).
    /// A text node's style is its parent element's ([`ComputedTable::style_of`]).
    pub styles: Vec<Option<ComputedStyle>>,
    /// The distinct `font-family` lists, which [`ComputedStyle::font_family`] indexes; the
    /// first is the initial `serif`.
    pub families: Vec<Vec<Family>>,
}

impl ComputedTable {
    /// The computed style of element `node`, if it has one.
    pub fn get(&self, node: usize) -> Option<&ComputedStyle> {
        self.styles.get(node).and_then(Option::as_ref)
    }

    /// The style that applies to `node`: its own if it is an element, else its parent's
    /// (CSS Cascade 4 §7.2: text "inherits" from its parent element), given `parent`, the
    /// arena's parent of `node`.
    pub fn style_of(&self, node: usize, parent: Option<usize>) -> Option<&ComputedStyle> {
        self.get(node).or_else(|| parent.and_then(|p| self.get(p)))
    }

    /// The family list `style.font_family` names; empty if the index is out of range.
    pub fn family(&self, style: &ComputedStyle) -> &[Family] {
        self.families
            .get(style.font_family)
            .map_or(&[], Vec::as_slice)
    }
}
