//! Min-content and max-content widths: CSS 2.1 §10.3.5's "preferred
//! minimum width" and "preferred width", which the shrink-to-fit width of
//! inline blocks (§10.3.9) and of the table placeholder reads (phase-5.md
//! item 5.14).
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

use std::collections::HashMap;

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::{ComputedStyle, Lp, MaxSize, Size};

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

/// The intrinsic sizes of every box of `tree` (see the module's modelling
/// choices); `ifcs` holds each inline formatting context by container, and
/// `role` says what each box is to the walk.
pub fn sizes(
    tree: &BoxTree,
    styles: &[ComputedStyle],
    ifcs: &HashMap<BoxId, Ifc>,
    role: &dyn Fn(BoxId) -> Role,
    fonts: &impl TextFns,
    arena: &Arena,
) -> Intrinsic {
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
            _ if matches!(role(b), Role::Flow | Role::Atomic | Role::Root) => {
                let c = if let Some(ifc) = ifcs.get(&b) {
                    line_sizes(ifc, styles, &|a| outer.get(a).copied().unwrap_or((0, 0)))
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
