//! Min-content and max-content widths: CSS 2.1 §10.3.5's "preferred
//! minimum width" and "preferred width", which the shrink-to-fit width of
//! inline blocks (§10.3.9) reads (phase-5.md item 5.14), and the table
//! measures of item 5.15 read.
//!
//! Source: CSS 2.1 §10.3.5 ("Roughly: calculate the preferred width by
//! formatting the content without breaking lines other than where explicit
//! line breaks occur, and also calculate the preferred minimum width, e.g.,
//! by trying all possible line breaks. CSS 2.1 does not define the exact
//! algorithm"); the line contents' sizes are item 5.12's `min_content` and
//! `max_content` (CSS Text 3 §5, §5.4).
//!
//! Modelling choices:
//!
//! - **One pass from the leaves up**: the tree's ids are in tree order, so
//!   visiting them from the last to the first visits every box after its
//!   descendants. Each box's *outer* sizes are its content's sizes, or its
//!   `width` when that is a length, clamped by its `min-width` and
//!   `max-width` lengths, plus its horizontal borders, padding and margins
//!   (percentages and `auto` count as zero, as CSS Sizing 3† has them in
//!   intrinsic sizes).
//! - **A block container with block-level children** has the largest of
//!   its in-flow children's outer sizes (markers, columns and inline content
//!   aside); **one with inline content** item 5.12's sizes of its lines, with
//!   each atomic inline's outer sizes as its unit's advance.
//! - **A replaced element** has its used width with no containing block
//!   (percentages as zero) as both sizes.
//! - **Tables** (item 5.15): a table cell's content sizes are a block
//!   container's (with the Quirks Mode Standard's §3.8 in quirks mode); a
//!   table box's content sizes are its columns' (`table/measure.rs`: the
//!   sums of their min-content and max-content widths with the border
//!   spacing, or fixed layout's lengths), so its outer sizes are GRIDMIN
//!   and GRIDMAX; a table wrapper box's are CSS Tables 3 §3.9.1's used
//!   width with no room and with unlimited room (`measure::table_intrinsic`),
//!   from its table's and captions' outer sizes and the table's `width` and
//!   `min-width`, which it holds. Rows and row groups have none.

use std::collections::HashMap;

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::{ComputedStyle, Lp, MaxSize, Size};

use crate::boxes::Class;
use crate::boxes::replaced::Replaced;
use crate::table::grid::Grid;
use crate::table::measure::{self, Inputs};
use crate::table::state::TableWidthInput;

use super::fonts::TextFns;
use super::inline::{Ifc, intrinsic as line_sizes};

use super::replaced::{natural, used_width};
use super::state::Role;
use crate::boxes::{BoxId, BoxKind, BoxTree};

/// A length that is not a percentage, else zero.
fn fixed(v: Lp) -> i32 {
    match v {
        Lp::Px64(x) => x,
        Lp::Percent(_) => 0,
    }
}

/// `auto` and percentages as zero.
fn fixed_size(v: Size) -> i32 {
    match v {
        Size::Lp(x) => fixed(x),
        Size::Auto => 0,
    }
}

/// The horizontal borders, padding and margins of style `s`, with
/// percentages and `auto` as zero.
fn outer_edges(s: &ComputedStyle) -> i32 {
    let [_, br, _, bl] = s.border_width;
    let [_, pr, _, pl] = s.padding;
    let [_, mr, _, ml] = s.margin;
    [br, bl, fixed(pr), fixed(pl), fixed_size(mr), fixed_size(ml)]
        .iter()
        .fold(0i32, |a, &x| a.saturating_add(x))
}

/// Content sizes `(min, max)` replaced by a fixed `width`, clamped by the
/// fixed `min-width` and `max-width`.
fn constrain(s: &ComputedStyle, (min, max): (i32, i32)) -> (i32, i32) {
    let (mut lo, mut hi) = match s.width {
        Size::Lp(Lp::Px64(w)) => (w, w),
        _ => (min, max),
    };
    if let MaxSize::Lp(Lp::Px64(m)) = s.max_width {
        lo = lo.min(m);
        hi = hi.min(m);
    }
    if let Size::Lp(Lp::Px64(m)) = s.min_width {
        lo = lo.max(m);
        hi = hi.max(m);
    }
    (lo.max(0), hi.max(lo).max(0))
}

/// Every box's outer `(min-content, max-content)` widths, and every block
/// container's content sizes, indexed by box id (zeros for boxes that do
/// not have them).
pub struct Intrinsic {
    /// Outer sizes.
    pub outer: Vec<(i32, i32)>,
    /// Content sizes.
    pub content: Vec<(i32, i32)>,
}

/// What the intrinsic sizes read about tables (item 5.15).
pub struct Tables<'a> {
    /// Each table box's grid.
    pub grids: &'a HashMap<BoxId, Grid>,
    /// The document is in quirks mode.
    pub quirks: bool,
}

/// The intrinsic sizes of every box of `tree` (see the module's modelling
/// choices); `ifcs` holds each inline formatting context by container,
/// `role` says what each box is to the walk, and `tables` what tables need.
pub fn sizes(
    tree: &BoxTree,
    styles: &[ComputedStyle],
    ifcs: &HashMap<BoxId, Ifc>,
    role: &dyn Fn(BoxId) -> Role,
    fonts: &impl TextFns,
    arena: &Arena,
    tables: &Tables<'_>,
) -> Intrinsic {
    let (grids, quirks) = (tables.grids, tables.quirks);
    let n = tree.boxes.len();
    let mut outer = vec![(0i32, 0i32); n];
    let mut content = vec![(0i32, 0i32); n];
    let initial = ComputedStyle::initial();
    for b in (0..n).rev() {
        let Some(lb) = tree.get(b) else { continue };
        let s = styles.get(b).unwrap_or(&initial);
        let own = match &lb.kind {
            BoxKind::Replaced { what, .. } => {
                let w = used_width(natural(what, s, fonts, arena, lb.node), s, 0);
                (w, w)
            }
            BoxKind::Table { .. } => {
                let c = table_sizes(tree, arena, styles, &content, grids, quirks, b);
                if let Some(slot) = content.get_mut(b) {
                    *slot = c;
                }
                c
            }
            BoxKind::TableWrapper { .. } => {
                let c = wrapper_sizes(tree, s, &outer, b);
                if let Some(slot) = content.get_mut(b) {
                    *slot = c;
                }
                c
            }
            _ if matches!(role(b), Role::Flow | Role::Atomic | Role::Root | Role::Cell) => {
                let c = if let Some(ifc) = ifcs.get(&b) {
                    // The Quirks Mode Standard's §3.8: "if cell has a computed
                    // value of the 'width' property that is 'auto'".
                    let is_image = |a: BoxId| {
                        matches!(
                            tree.get(a).map(|x| &x.kind),
                            Some(BoxKind::Replaced {
                                what: Replaced::Image,
                                inline: true,
                            })
                        )
                    };
                    let quirk = quirks && role(b) == Role::Cell && matches!(s.width, Size::Auto);
                    line_sizes(
                        ifc,
                        styles,
                        &|a| outer.get(a).copied().unwrap_or((0, 0)),
                        quirk.then_some(&is_image as &dyn Fn(BoxId) -> bool),
                    )
                } else {
                    lb.children
                        .iter()
                        .filter(|&&c| matches!(role(c), Role::Flow))
                        .fold((0i32, 0i32), |(lo, hi), &c| {
                            let (a, z) = outer.get(c).copied().unwrap_or((0, 0));
                            (lo.max(a), hi.max(z))
                        })
                };
                if let Some(slot) = content.get_mut(b) {
                    *slot = c;
                }
                constrain(s, c)
            }
            _ => continue,
        };
        let e = outer_edges(s);
        if let Some(slot) = outer.get_mut(b) {
            *slot = (own.0.saturating_add(e), own.1.saturating_add(e));
        }
    }

    Intrinsic { outer, content }
}

/// Table box `t`'s content sizes: its columns' widths with the border
/// spacing (item 5.15).
fn table_sizes(
    tree: &BoxTree,
    arena: &Arena,
    styles: &[ComputedStyle],
    content: &[(i32, i32)],
    grids: &HashMap<BoxId, Grid>,
    quirks: bool,
    t: BoxId,
) -> (i32, i32) {
    let Some(grid) = grids.get(&t).filter(|g| g.has_slots()) else {
        return (0, 0);
    };
    let s = styles.get(t);
    let hs = s
        .filter(|s| !s.border_collapse)
        .map_or(0, |s| s.border_spacing[0].max(0));
    let x = Inputs {
        tree,
        arena,
        styles,
        content,
        quirks,
    };
    if crate::table::is_fixed(tree, styles, t) {
        let w = measure::fixed_sizes(&measure::fixed_columns(grid, &x, hs), hs);
        (w, w)
    } else {
        measure::grid_sizes(&measure::columns(grid, &x, hs), hs)
    }
}

/// Table wrapper box `w`'s content sizes (style `s`, which holds its
/// table's `width` and `min-width`): CSS Tables 3 §3.9.1's used width of its
/// table with no room and with unlimited room (item 5.15).
fn wrapper_sizes(tree: &BoxTree, s: &ComputedStyle, outer: &[(i32, i32)], w: BoxId) -> (i32, i32) {
    let children = tree.children(w);
    let table = children
        .iter()
        .copied()
        .find(|&c| matches!(tree.class(c), Class::Table { .. }));
    let (gridmin, gridmax) = table.and_then(|t| outer.get(t).copied()).unwrap_or((0, 0));
    let capmin = children
        .iter()
        .filter(|&&c| tree.class(c) == Class::Caption)
        .map(|&c| outer.get(c).map_or(0, |o| o.0))
        .max()
        .unwrap_or(0);
    measure::table_intrinsic(TableWidthInput {
        gridmin,
        gridmax,
        capmin,
        min_width: fixed_size(s.min_width),
        // A percentage `width` counts as `auto` here.
        width: match s.width {
            Size::Lp(Lp::Px64(v)) => Some(v),
            _ => None,
        },
        available: 0,
    })
}
