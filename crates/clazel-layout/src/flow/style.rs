//! Each box's computed style, as formatting reads it (phase-5.md item
//! 5.14).
//!
//! Sources: CSS 2.1 §9.2.1.1 and §9.2.2.1 ("The properties of anonymous
//! boxes are inherited from the enclosing non-anonymous box. Non-inherited
//! properties have their initial value"), §17.2.1's anonymous table objects
//! (likewise), §17.4 ("The computed values of properties 'position',
//! 'float', 'margin-*', 'top', 'right', 'bottom', and 'left' on the table
//! element are used on the table wrapper box and not the table box; all
//! other values of non-inheritable properties are used on the table box and
//! not the table wrapper box"), and §8.3 and §8.4 with §17.5's tables
//! ("margins … apply to all elements except elements with table display
//! types other than table-caption, table and inline-table").
//!
//! Modelling choices:
//!
//! - **A box with a node that has a computed style takes it**; any other
//!   box (an anonymous box, a text run, whose node is a text node) takes
//!   its parent box's inherited properties and initial values for the rest.
//!   A text run thus has its parent element's font and text properties, as
//!   CSS Cascade 4 §7.2† has text inherit them.
//! - **The inherited properties of the subset** are `color`, the `font-*`
//!   properties, `line-height`, `text-align`, `text-indent`, `white-space`,
//!   `overflow-wrap`, `word-break`, `visibility`, `border-spacing`,
//!   `border-collapse` and `list-style-type` (each property's definition
//!   table, "Inherited: yes").
//! - **The table wrapper box** takes the table's margins, as §17.4 says, and
//!   also holds its `width`, `min-width` and `max-width`, which item 5.15
//!   reads there as the table's to size the wrapper ("The width of the table
//!   wrapper box is the border-edge width of the table box inside it"); its
//!   borders, padding and background are the table box's. **The table box**
//!   has no margins and an `auto` width, so it fills its wrapper.
//! - **Row groups, rows and cells have no margins** (§8.3).

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::Lp;
use clazel_style::cascade::computed::{ComputedStyle, LineStyle, MaxSize, Size, TRANSPARENT};

use crate::boxes::{BoxKind, BoxTree, StyleFns};

/// `style` with every property but the inherited ones set to its initial
/// value: what an anonymous box under a box of style `style` has.
pub fn inherit(style: &ComputedStyle) -> ComputedStyle {
    ComputedStyle {
        color: style.color,
        font_family: style.font_family,
        font_size: style.font_size,
        font_weight: style.font_weight,
        font_style: style.font_style,
        line_height: style.line_height,
        text_align: style.text_align,
        text_indent: style.text_indent,
        white_space: style.white_space,
        overflow_wrap: style.overflow_wrap,
        word_break: style.word_break,
        visibility: style.visibility,
        border_spacing: style.border_spacing,
        border_collapse: style.border_collapse,
        list_style_type: style.list_style_type.clone(),
        ..ComputedStyle::initial()
    }
}

/// No margins.
const NO_MARGIN: [Size; 4] = [Size::Lp(Lp::Px64(0)); 4];

/// The computed style of every box of `tree` (see the module's modelling
/// choices). The tree's ids are in tree order (item 5.13's `compact`), so a
/// parent's style is known before its children's.
pub fn box_styles(tree: &BoxTree, styles: &impl StyleFns) -> Vec<ComputedStyle> {
    let mut out: Vec<ComputedStyle> = Vec::with_capacity(tree.boxes.len());
    for b in &tree.boxes {
        let parent = b.parent.and_then(|p| out.get(p));
        let own = b.node.and_then(|n| styles.style(n));
        let mut s = match (own, parent) {
            (Some(s), _) if !matches!(b.kind, BoxKind::Text(_)) => s.clone(),
            (_, Some(p)) => inherit(p),
            (_, None) => ComputedStyle::initial(),
        };
        match b.kind {
            BoxKind::TableWrapper { .. } => {
                s.border_width = [0; 4];
                s.border_style = [LineStyle::None; 4];
                s.padding = [Lp::Px64(0); 4];
                s.background_color = TRANSPARENT;
                s.height = Size::Auto;
                s.min_height = Size::Auto;
                s.max_height = MaxSize::None;
            }
            BoxKind::Table { .. } => {
                s.margin = NO_MARGIN;
                s.width = Size::Auto;
                s.min_width = Size::Auto;
                s.max_width = MaxSize::None;
            }
            BoxKind::RowGroup(_) | BoxKind::Row | BoxKind::Cell => {
                s.margin = NO_MARGIN;
            }
            _ => {}
        }
        out.push(s);
    }
    out
}

/// Whether node `node` of `arena` is an HTML element named `name`.
pub fn is_html(arena: &Arena, node: Option<usize>, name: &str) -> bool {
    node.is_some_and(|n| clazel_style::cascade::hints::is_html(arena, n, name))
}
