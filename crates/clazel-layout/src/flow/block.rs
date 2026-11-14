//! The layout walk (phase-5.md item 5.14): block formatting contexts
//! (CSS 2.1 §9.4.1) with margin collapsing (§8.3.1), widths top down
//! (§10.3), heights bottom up (§10.6), inline formatting contexts' lines at
//! their container's end (§9.4.2), the Quirks Mode Standard's §3.5 to §3.7,
//! and HTML's "align descendants"; then every position made absolute.
//!
//! Sources: CSS 2.1 (W3C Recommendation, 7 June 2011) §8.3.1, §9.4.1,
//! §10.1, §10.3.3, §10.3.4, §10.3.9, §10.3.10, §10.6.3, §10.6.6, §10.6.7;
//! the Quirks Mode Standard (commit `5a06deb5`) §3.5 to §3.7; HTML at commit
//! `4c54fae1` §15.2 ("align descendants") and §15.3.3.
//!
//! Modelling choices:
//!
//! - **One walk, an explicit stack of tasks** ([`Task`]): entering a box
//!   gives its used width, horizontal margins and top margin from its
//!   containing block's width (top down); exiting it, after its children,
//!   gives its height (bottom up). A block container keeps a [`Frame`] on a
//!   second stack while its children are laid out, holding its [`Flow`].
//!   Nothing recurses, so a document of any depth lays out.
//! - **The resolution walk**: when content is placed (a box whose border
//!   box is content, or a line box that is not empty), the open frames
//!   above it on the stack (`state.rs`) are closed from the outermost in:
//!   the outermost is placed in its parent's flow after the pending margins,
//!   every inner one at the top of its parent's content, and the content at
//!   the top of the innermost. Each frame is closed once, so the walk is
//!   linear in the tree's size over the whole layout.
//! - **A box whose margins collapse through it** is placed where §8.3.1
//!   says: at its parent's content top if its parent is still open (its top
//!   margin collapsed with its parent's), else after the margins before it
//!   and its own top margin, "as if the element had a non-zero bottom
//!   border".
//! - **Block formatting context roots** (§9.4.1): the root element ("Margins
//!   of the root element's box do not collapse"), inline blocks, table cells,
//!   captions, the table placeholder's boxes (`mod.rs`), and block boxes
//!   whose `overflow` is not `visible` "except when that value has been
//!   propagated to the viewport": the root element's `overflow` always is,
//!   and the `body`'s is when the root element's is `visible` (CSS 2.1
//!   §11.1.1†).
//! - **"Align descendants"** (HTML §15.2) is applied to a block-level box
//!   whose two horizontal margins are not `auto`, using the nearest ancestor
//!   that aligns descendants, unless the box itself has an applicable `align`
//!   attribute (an element that aligns descendants other than `center`).
//! - **The quirks** apply in quirks mode, and §3.3 and §3.4 also in
//!   limited-quirks mode, as the standard says; §3.6 to the box of the
//!   document element when it is an `html` element, and §3.7 to the
//!   principal box of "the document's body element" when it is block-level.

use std::collections::HashMap;
use std::ops::Range;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::DocumentMode;
use clazel_style::cascade::computed::{AlignDescendants, ComputedStyle, Overflow};

use super::Viewport;
use super::fonts::TextFns;
use super::fragment::{BoxFragment, FragmentTree, Glyph, GlyphRun, LineBox, LineItem, Rect, Sides};
use super::heights::{child_basis, min_max, quirk_fill};
use super::inline::{
    AtomicSize, Ifc, LineContext, has_inline_content, layout_lines, prepare, union,
};
use super::intrinsic::{Intrinsic, sizes};
use super::length::{lp, max_size_opt, size, size_opt};
use super::margins::{close, enter, exit, finish, place};
use super::replaced::{natural, used_height, used_width};
use super::state::{
    Align, BlockFacts, Collapsed, Entry, Exited, Flow, Role, UsedWidths, WidthInput,
};
use super::style::{box_styles, is_html};
use super::widths::{align, min_max as width_min_max, shrink_to_fit, solve_block};
use crate::boxes::{BoxId, BoxKind, BoxTree, Class, StyleFns};

/// The document's mode, as the quirks read it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// No-quirks mode.
    NoQuirks,
    /// Limited-quirks mode: §3.3 and §3.4 apply.
    LimitedQuirks,
    /// Quirks mode: §3.3 to §3.7 apply.
    Quirks,
}

/// Whether a box of class `class` lays its content out in a flow of its
/// own: a block container, or a box of the table placeholder (`mod.rs`).
pub fn has_flow(class: Class) -> bool {
    matches!(
        class,
        Class::Root
            | Class::Block
            | Class::InlineBlock
            | Class::Cell
            | Class::Caption
            | Class::TableWrapper { .. }
            | Class::Table { .. }
            | Class::RowGroup
            | Class::Row
    )
}

/// What a box of class `class` is to the walk (`state.rs`'s contract).
pub fn role(class: Class) -> Role {
    match class {
        Class::Root => Role::Root,
        Class::Marker => Role::Marker,
        Class::Column | Class::ColumnGroup => Role::Column,
        Class::Inline | Class::Text { .. } => Role::Inline,
        Class::InlineBlock
        | Class::Replaced { inline: true }
        | Class::TableWrapper { inline: true } => Role::Atomic,
        // A table box is in its wrapper's flow, inline table or not.
        Class::Block
        | Class::Replaced { inline: false }
        | Class::TableWrapper { inline: false }
        | Class::Table { .. }
        | Class::RowGroup
        | Class::Row
        | Class::Cell
        | Class::Caption => Role::Flow,
    }
}

/// A box's geometry while laying out: its border box relative to its
/// positioning parent's content box (the nearest ancestor laid out as a
/// block container), and its used edges.
#[derive(Debug, Clone, Default)]
struct Geo {
    x: i32,
    y: i32,
    width: i32,
    height: i32,
    margin: Sides,
    border: Sides,
    padding: Sides,
    /// Baselines, from the border box's top.
    first: Option<i32>,
    last: Option<i32>,
    lines: Range<usize>,
    laid: bool,
    parent: Option<BoxId>,
}

/// A block container being laid out.
#[derive(Debug, Clone)]
struct Frame {
    owner: BoxId,
    flow: Flow,
    facts: BlockFacts,
    /// Its content width.
    width: i32,
    /// Its own `height`, when specified explicitly (content box).
    definite: Option<i32>,
    min_height: i32,
    max_height: Option<i32>,
    /// The percentage basis of its children's heights.
    basis: Option<i32>,
    /// The alignment its descendants get.
    align: Option<Align>,
    /// Baselines of its content so far, from its content box's top.
    first: Option<i32>,
    last: Option<i32>,
}

/// A task of the walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Task {
    Enter(BoxId),
    Exit(BoxId),
}

/// HTML's "align descendants" directions as `widths::align` reads them.
fn align_of(a: AlignDescendants) -> Align {
    match a {
        AlignDescendants::Left => Align::Left,
        AlignDescendants::Center => Align::Center,
        AlignDescendants::Right => Align::Right,
    }
}

/// A style's borders and padding against containing block width `cb`.
fn edges(s: &ComputedStyle, cb: i32) -> (Sides, Sides) {
    let [bt, br, bb, bl] = s.border_width;
    let [pt, pr, pb, pl] = s.padding;
    (
        Sides {
            top: bt,
            right: br,
            bottom: bb,
            left: bl,
        },
        Sides {
            top: lp(pt, cb),
            right: lp(pr, cb),
            bottom: lp(pb, cb),
            left: lp(pl, cb),
        },
    )
}

struct Walk<'a, F: TextFns> {
    tree: &'a BoxTree,
    arena: &'a Arena,
    fonts: &'a F,
    mode: Mode,
    viewport: Viewport,
    styles: Vec<ComputedStyle>,
    ifcs: HashMap<BoxId, Ifc>,
    intrinsic: Intrinsic,
    geo: Vec<Geo>,
    frames: Vec<Frame>,
    tasks: Vec<Task>,
    lines: Vec<LineBox>,
    /// The box whose content box each line box is relative to.
    line_origin: Vec<BoxId>,
    /// The document element's principal box.
    root_box: Option<BoxId>,
    /// It, when the document element is an `html` element (§3.6).
    html: Option<BoxId>,
    body: Option<BoxId>,
    /// The `html` box's content height as §3.6 makes it at least.
    html_fill: Option<i32>,
    /// The `body`'s `overflow` is propagated to the viewport.
    body_propagates: bool,
}

impl<F: TextFns> Walk<'_, F> {
    fn style(&self, b: BoxId) -> &ComputedStyle {
        // Every box has a style (`box_styles`); the root's is the first.
        self.styles
            .get(b)
            .or_else(|| self.styles.first())
            .unwrap_or_else(|| unreachable_style())
    }

    fn geo_mut(&mut self, b: BoxId) -> Option<&mut Geo> {
        self.geo.get_mut(b)
    }

    /// The resolution walk (the module's modelling choices) for content
    /// placed in the innermost frame after `margins`: the content's top in
    /// that frame's content box.
    fn resolve(&mut self, margins: Collapsed) -> i32 {
        let Some(k) = self.frames.len().checked_sub(1) else {
            return 0;
        };
        let innermost_open = self.frames.get(k).is_some_and(|f| f.flow.open);
        if !innermost_open {
            let Some(f) = self.frames.get_mut(k) else {
                return 0;
            };
            let (top, next) = place(f.flow, f.flow.pending.join(margins));
            f.flow = next;
            return top;
        }
        // The outermost open frame of the run at the top of the stack.
        let mut o = k;
        while let Some(prev) = o.checked_sub(1)
            && self.frames.get(prev).is_some_and(|f| f.flow.open)
        {
            o = prev;
        }
        let pending = self
            .frames
            .get(k)
            .map_or(Collapsed::NONE, |f| f.flow.pending)
            .join(margins);
        // Frame `o - 1` is closed (the root's frame never opens).
        let top = match o.checked_sub(1).and_then(|p| self.frames.get_mut(p)) {
            Some(parent) => {
                let (top, next) = place(parent.flow, pending);
                parent.flow = next;
                top
            }
            None => pending.resolve(),
        };
        for i in o..=k {
            let Some(f) = self.frames.get_mut(i) else {
                continue;
            };
            let mut closed = close(f.flow);
            closed.pending = Collapsed::NONE;
            f.flow = closed;
            let owner = f.owner;
            let y = if i == o { top } else { 0 };
            if let Some(g) = self.geo_mut(owner) {
                g.y = y;
            }
        }
        0
    }

    /// Pushes the tasks for `b`'s children: its atomic inlines if it has
    /// inline content, else its in-flow children.
    fn push_children(&mut self, b: BoxId) {
        if let Some(ifc) = self.ifcs.get(&b) {
            let atomics: Vec<BoxId> = ifc.atomics.iter().rev().copied().collect();
            self.tasks.extend(atomics.into_iter().map(Task::Enter));
            return;
        }
        let children: Vec<BoxId> = self
            .tree
            .children(b)
            .iter()
            .rev()
            .copied()
            .filter(|&c| role(self.tree.class(c)) == Role::Flow)
            .collect();
        self.tasks.extend(children.into_iter().map(Task::Enter));
    }

    /// Whether box `b` establishes a new block formatting context (§9.4.1;
    /// the module's modelling choices).
    fn bfc_root(&self, b: BoxId) -> bool {
        let class = self.tree.class(b);
        if !matches!(class, Class::Block) {
            return true;
        }
        if Some(b) == self.root_box {
            return true;
        }
        let s = self.style(b);
        let visible = s.overflow_x == Overflow::Visible && s.overflow_y == Overflow::Visible;
        !(visible || (Some(b) == self.body && self.body_propagates))
    }

    fn enter_root(&mut self, b: BoxId) {
        let (w, h) = (self.viewport.width, self.viewport.height);
        if let Some(g) = self.geo_mut(b) {
            *g = Geo {
                width: w,
                height: h,
                laid: true,
                ..Geo::default()
            };
        }
        self.frames.push(Frame {
            owner: b,
            flow: Flow::CLOSED,
            facts: BlockFacts {
                container: true,
                bfc_root: true,
                top_edge: false,
                bottom_edge: false,
                height_auto: false,
                height_zero: false,
                min_height_zero: true,
            },
            width: w,
            definite: Some(h),
            min_height: 0,
            max_height: None,
            // §10.5: "A percentage height on the root element is relative
            // to the initial containing block."
            basis: Some(h),
            align: None,
            first: None,
            last: None,
        });
        self.tasks.push(Task::Exit(b));
        self.push_children(b);
    }

    /// The used widths of in-flow block-level box `b` (§10.3.3, §10.3.4,
    /// the table placeholder; §10.4; align descendants).
    fn block_widths(
        &self,
        b: BoxId,
        cb: i32,
        edges_h: i32,
        parent_align: Option<Align>,
    ) -> UsedWidths {
        let s = self.style(b);
        let [_, mr, _, ml] = s.margin;
        let ml = size(ml, cb);
        let mr = size(mr, cb);
        let width = match &self.tree.get(b).map(|x| &x.kind) {
            Some(BoxKind::Replaced { what, .. }) => {
                // §10.3.4: "The used value of 'width' is determined as for
                // inline replaced elements."
                let n = natural(
                    what,
                    s,
                    self.fonts,
                    self.arena,
                    self.tree.get(b).and_then(|x| x.node),
                );
                Some(used_width(n, s, cb))
            }
            Some(BoxKind::TableWrapper { .. }) => Some(size(s.width, cb).unwrap_or_else(|| {
                // The placeholder: shrink-to-fit, as an inline block's.
                let (lo, hi) = self.intrinsic.content.get(b).copied().unwrap_or((0, 0));
                let available = cb
                    .saturating_sub(ml.unwrap_or(0))
                    .saturating_sub(mr.unwrap_or(0))
                    .saturating_sub(edges_h);
                shrink_to_fit(lo, hi, available)
            })),
            _ => size(s.width, cb),
        };
        let input = WidthInput {
            containing: cb,
            margin_left: ml,
            margin_right: mr,
            edges: edges_h,
            width,
        };
        let mut used = solve_block(input);
        if !matches!(self.tree.class(b), Class::Replaced { .. }) {
            // §10.4: percentages of a negative containing block width are 0.
            let basis = Some(cb.max(0));
            let min = size_opt(s.min_width, basis).unwrap_or(0);
            let max = max_size_opt(s.max_width, basis);
            if let Some(again) = width_min_max(used.width, min, max) {
                used = solve_block(WidthInput {
                    width: Some(again),
                    ..input
                });
            }
        }
        // HTML §15.2: only boxes whose margins are both not `auto`, and not
        // one with an applicable align attribute of its own.
        let own_align = s.align_descendants.is_some()
            && !is_html(self.arena, self.tree.get(b).and_then(|x| x.node), "center");
        // Margins do not apply to the table-internal boxes of the
        // placeholder (§8.3), so they are never over-constrained.
        if let Some(a) = parent_align
            && ml.is_some()
            && mr.is_some()
            && !own_align
            && self.tree.class(b).is_block_level()
        {
            used = align(used, a);
        }
        used
    }

    fn enter_flow(&mut self, b: BoxId) {
        let Some(parent) = self.frames.last().cloned() else {
            return;
        };
        let cb = parent.width;
        let s = self.style(b).clone();
        let (border, padding) = edges(&s, cb);
        let edges_h = border.horizontal().saturating_add(padding.horizontal());
        let used = self.block_widths(b, cb, edges_h, parent.align);
        // §10.6.3, §10.6.6: "If 'margin-top', or 'margin-bottom' are 'auto',
        // their used value is 0."
        let mt = size(s.margin[0], cb).unwrap_or(0);
        let mb = size(s.margin[2], cb).unwrap_or(0);
        let class = self.tree.class(b);
        let replaced = matches!(class, Class::Replaced { .. });
        let definite = size_opt(s.height, parent.basis);
        let min_height = size_opt(s.min_height, parent.basis).unwrap_or(0);
        let max_height = max_size_opt(s.max_height, parent.basis);
        let facts = BlockFacts {
            container: !replaced,
            bfc_root: self.bfc_root(b),
            top_edge: border.top != 0 || padding.top != 0,
            bottom_edge: border.bottom != 0 || padding.bottom != 0,
            height_auto: definite.is_none(),
            height_zero: definite == Some(0),
            min_height_zero: min_height == 0,
        };
        let mut height = 0;
        if replaced && let Some(BoxKind::Replaced { what, .. }) = self.tree.get(b).map(|x| &x.kind)
        {
            let n = natural(
                what,
                &s,
                self.fonts,
                self.arena,
                self.tree.get(b).and_then(|x| x.node),
            );
            height = used_height(n, &s, parent.basis)
                .saturating_add(border.vertical())
                .saturating_add(padding.vertical());
        }
        if let Some(g) = self.geo_mut(b) {
            *g = Geo {
                x: used.margin_left,
                y: 0,
                width: used.width.saturating_add(edges_h),
                height,
                margin: Sides {
                    top: mt,
                    right: used.margin_right,
                    bottom: mb,
                    left: used.margin_left,
                },
                border,
                padding,
                laid: true,
                parent: Some(parent.owner),
                ..Geo::default()
            };
        }
        let (entry, pflow) = enter(parent.flow, facts, mt);
        if let Some(p) = self.frames.last_mut() {
            p.flow = pflow;
        }
        let flow = match entry {
            Entry::Open(m) => Flow::open(m),
            Entry::Content(m) => {
                let top = self.resolve(m);
                if let Some(g) = self.geo_mut(b) {
                    g.y = top;
                }
                Flow::CLOSED
            }
        };
        self.tasks.push(Task::Exit(b));
        if replaced {
            return;
        }
        let quirks = self.mode == Mode::Quirks;
        let passes_on = !matches!(class, Class::Cell | Class::TableWrapper { .. });
        let own_definite = definite.map(|h| min_max(h, min_height, max_height));
        self.frames.push(Frame {
            owner: b,
            flow,
            facts,
            width: used.width,
            definite,
            min_height,
            max_height,
            basis: child_basis(own_definite, quirks, passes_on, parent.basis),
            align: s.align_descendants.map(align_of).or(parent.align),
            first: None,
            last: None,
        });
        self.push_children(b);
    }

    fn enter_atomic(&mut self, b: BoxId) {
        let Some(parent) = self.frames.last().cloned() else {
            return;
        };
        let cb = parent.width;
        let s = self.style(b).clone();
        let (border, padding) = edges(&s, cb);
        let edges_h = border.horizontal().saturating_add(padding.horizontal());
        // §10.3.9, §10.3.2: "A computed value of 'auto' for 'margin-left' or
        // 'margin-right' becomes a used value of '0'"; §10.6.2, §10.6.6 for
        // the vertical ones.
        let m = |i: usize| s.margin.get(i).and_then(|&v| size(v, cb)).unwrap_or(0);
        let margin = Sides {
            top: m(0),
            right: m(1),
            bottom: m(2),
            left: m(3),
        };
        let basis = Some(cb.max(0));
        let kind = self.tree.get(b).map(|x| x.kind.clone());
        let mut height = 0;
        let width = if let Some(BoxKind::Replaced { what, .. }) = &kind {
            // §10.3.10: "Exactly as inline replaced elements."
            let n = natural(
                what,
                &s,
                self.fonts,
                self.arena,
                self.tree.get(b).and_then(|x| x.node),
            );
            height = used_height(n, &s, parent.basis)
                .saturating_add(border.vertical())
                .saturating_add(padding.vertical());
            used_width(n, &s, cb)
        } else {
            // §10.3.9: "If 'width' is 'auto', the used value is the
            // shrink-to-fit width as for floating elements."
            let tentative = size(s.width, cb).unwrap_or_else(|| {
                let (lo, hi) = self.intrinsic.content.get(b).copied().unwrap_or((0, 0));
                let available = cb
                    .saturating_sub(margin.horizontal())
                    .saturating_sub(edges_h);
                shrink_to_fit(lo, hi, available)
            });
            let min = size_opt(s.min_width, basis).unwrap_or(0);
            let max = max_size_opt(s.max_width, basis);
            width_min_max(tentative, min, max)
                .unwrap_or(tentative)
                .max(0)
        };
        if let Some(g) = self.geo_mut(b) {
            *g = Geo {
                width: width.saturating_add(edges_h),
                height,
                margin,
                border,
                padding,
                laid: true,
                parent: Some(parent.owner),
                ..Geo::default()
            };
        }
        self.tasks.push(Task::Exit(b));
        if matches!(kind, Some(BoxKind::Replaced { .. })) {
            return;
        }
        let definite = size_opt(s.height, parent.basis);
        let min_height = size_opt(s.min_height, parent.basis).unwrap_or(0);
        let max_height = max_size_opt(s.max_height, parent.basis);
        let own_definite = definite.map(|h| min_max(h, min_height, max_height));
        self.frames.push(Frame {
            owner: b,
            flow: Flow::CLOSED,
            facts: BlockFacts {
                container: true,
                bfc_root: true,
                top_edge: border.top != 0 || padding.top != 0,
                bottom_edge: border.bottom != 0 || padding.bottom != 0,
                height_auto: definite.is_none(),
                height_zero: definite == Some(0),
                min_height_zero: min_height == 0,
            },
            width,
            definite,
            min_height,
            max_height,
            basis: child_basis(own_definite, self.mode == Mode::Quirks, false, parent.basis),
            align: s.align_descendants.map(align_of).or(parent.align),
            first: None,
            last: None,
        });
        self.push_children(b);
    }

    /// Lays out the lines of the inline formatting context of the frame on
    /// top of the stack.
    fn lines(&mut self, b: BoxId) {
        let Some(ifc) = self.ifcs.get(&b) else {
            return;
        };
        let Some(frame) = self.frames.last() else {
            return;
        };
        let anonymous = self.tree.get(b).is_some_and(|x| x.node.is_none());
        let first_child = self
            .tree
            .get(b)
            .and_then(|x| x.parent)
            .is_some_and(|p| self.tree.children(p).first() == Some(&b));
        let geo = &self.geo;
        let atomic = |a: BoxId| -> AtomicSize {
            let Some(g) = geo.get(a) else {
                return AtomicSize::default();
            };
            let top_to_border = g.margin.top;
            AtomicSize {
                width: g.width.saturating_add(g.margin.horizontal()).max(0),
                height: g.height.saturating_add(g.margin.vertical()).max(0),
                baseline: g.last.map(|l| top_to_border.saturating_add(l)),
                margin_left: g.margin.left,
                margin_top: g.margin.top,
            }
        };
        let cx = LineContext {
            tree: self.tree,
            styles: &self.styles,
            fonts: self.fonts,
            quirks: self.mode != Mode::NoQuirks,
            width: frame.width,
            indent_first: !anonymous || first_child,
            atomic: &atomic,
        };
        let out = layout_lines(ifc, &cx);
        let top = if out.content {
            self.resolve(Collapsed::NONE)
        } else {
            self.frames.last().map_or(0, |f| f.flow.y)
        };
        let start = self.lines.len();
        for mut line in out.lines {
            line.rect.y = line.rect.y.saturating_add(top);
            line.baseline = line.baseline.saturating_add(top);
            for item in &mut line.items {
                match item {
                    LineItem::Text(r) => r.baseline = r.baseline.saturating_add(top),
                    LineItem::Inline(p) => p.rect.y = p.rect.y.saturating_add(top),
                    LineItem::Atomic(_) => {}
                }
            }
            self.lines.push(line);
            self.line_origin.push(b);
        }
        let end = self.lines.len();
        if let Some(g) = self.geo_mut(b) {
            g.lines = start..end;
        }
        for (a, x, y) in out.atomics {
            if let Some(g) = self.geo_mut(a) {
                g.x = x;
                g.y = y.saturating_add(top);
                g.parent = Some(b);
            }
        }
        for (i, r) in out.inlines {
            let cb = self.frames.last().map_or(0, |f| f.width);
            let e = self
                .styles
                .get(i)
                .map(|s| super::inline::inline_edges(s, cb))
                .unwrap_or_default();
            if let Some(g) = self.geo_mut(i) {
                *g = Geo {
                    x: r.x,
                    y: r.y.saturating_add(top),
                    width: r.width,
                    height: r.height,
                    margin: e.margin,
                    border: e.border,
                    padding: e.padding,
                    laid: true,
                    parent: Some(b),
                    ..Geo::default()
                };
            }
        }
        if let Some(f) = self.frames.last_mut() {
            if out.content {
                f.flow.y = top.saturating_add(out.height);
                f.flow.placed = true;
            }
            f.first = out.first_baseline.map(|v| v.saturating_add(top));
            f.last = out.last_baseline.map(|v| v.saturating_add(top));
        }
    }

    /// Places list item `b`'s marker beside its first line (`mod.rs`).
    fn marker(&mut self, b: BoxId, first: Option<i32>) {
        let Some(&mk) = self
            .tree
            .children(b)
            .iter()
            .find(|&&c| self.tree.class(c) == Class::Marker)
        else {
            return;
        };
        let Some(BoxKind::Marker(m)) = self.tree.get(mk).map(|x| &x.kind) else {
            return;
        };
        let s = self.style(mk).clone();
        let glyphs = self.fonts.shape(&s, &m.text);
        let metrics = self.fonts.metrics(&s);
        let width = glyphs.iter().fold(0i32, |a, g| a.saturating_add(g.advance));
        let baseline = first.unwrap_or(metrics.ascent);
        let x = width.saturating_neg();
        let mut pen = 0i32;
        let mut run = GlyphRun {
            source: mk,
            face: glyphs.first().map_or(0, |g| g.face),
            size: s.font_size,
            x,
            baseline,
            glyphs: Vec::new(),
        };
        for (unit, g) in glyphs.iter().enumerate() {
            run.glyphs.push(Glyph {
                id: g.id,
                x: pen.saturating_add(g.x_offset),
                y: g.y_offset,
                advance: g.advance,
                unit,
            });
            pen = pen.saturating_add(g.advance);
        }
        let rect = Rect {
            x,
            y: baseline.saturating_sub(metrics.ascent),
            width,
            height: metrics.ascent.saturating_add(metrics.descent),
        };
        let start = self.lines.len();
        self.lines.push(LineBox {
            container: mk,
            rect,
            baseline,
            items: vec![LineItem::Text(run)],
        });
        self.line_origin.push(b);
        if let Some(g) = self.geo_mut(mk) {
            *g = Geo {
                x: rect.x,
                y: rect.y,
                width: rect.width,
                height: rect.height,
                laid: true,
                parent: Some(b),
                lines: start..start.saturating_add(1),
                ..Geo::default()
            };
        }
    }

    /// Exits block container `b`, whose frame is on top of the stack.
    fn exit_container(&mut self, b: BoxId, in_flow: bool) {
        self.lines(b);
        let Some(frame) = self.frames.last().cloned() else {
            return;
        };
        let fin = finish(frame.flow, frame.facts);
        if fin.resolve {
            self.resolve(Collapsed::NONE);
        }
        self.frames.pop();
        let (border, padding, margin) = self
            .geo
            .get(b)
            .map(|g| (g.border, g.padding, g.margin))
            .unwrap_or_default();
        let bp = border.vertical().saturating_add(padding.vertical());
        let mut content = min_max(
            frame.definite.unwrap_or(fin.content),
            frame.min_height,
            frame.max_height,
        );
        if self.mode == Mode::Quirks && frame.definite.is_none() {
            let normal = content.saturating_add(bp);
            let margins = margin.vertical();
            let filled = if Some(b) == self.html {
                // §3.6: "Let size be the size of the initial containing
                // block in the block flow direction minus margins."
                Some(quirk_fill(normal, self.viewport.height, margins))
            } else if Some(b) == self.body {
                // §3.7: "Let size be the size of body's parent element's
                // content box in the block flow direction minus margins."
                self.html_fill.map(|h| quirk_fill(normal, h, margins))
            } else {
                None
            };
            if let Some(f) = filled {
                content = f.saturating_sub(bp).max(0);
            }
        }
        // Columns and column groups of the placeholder: empty, at the top.
        let columns: Vec<BoxId> = self
            .tree
            .children(b)
            .iter()
            .copied()
            .filter(|&c| role(self.tree.class(c)) == Role::Column)
            .collect();
        for c in columns {
            if let Some(g) = self.geo_mut(c) {
                *g = Geo {
                    laid: true,
                    parent: Some(b),
                    ..Geo::default()
                };
            }
        }
        let content_top = border.top.saturating_add(padding.top);
        if let Some(g) = self.geo_mut(b) {
            g.height = content.saturating_add(bp);
            g.first = frame.first.map(|v| v.saturating_add(content_top));
            g.last = frame.last.map(|v| v.saturating_add(content_top));
        }
        self.marker(b, frame.first);
        if !in_flow {
            return;
        }
        let Some(parent) = self.frames.last().cloned() else {
            return;
        };
        let geo = self.geo.get(b).cloned().unwrap_or_default();
        let pflow = if fin.through {
            // §8.3.1: at the parent's top if the top margin collapsed with
            // the parent's, else "as if the element had a non-zero bottom
            // border".
            let y = if parent.flow.open {
                0
            } else {
                parent.flow.y.saturating_add(fin.out.resolve())
            };
            if let Some(g) = self.geo_mut(b) {
                g.y = y;
            }
            exit(parent.flow, Exited::Through(fin.out.adjoin(margin.bottom)))
        } else {
            let bottom = geo.y.saturating_add(geo.height);
            let pending = if frame.facts.bottom_adjoins() {
                fin.out.adjoin(margin.bottom)
            } else {
                Collapsed::of(margin.bottom)
            };
            exit(parent.flow, Exited::Placed { bottom, pending })
        };
        let first = geo.first.map(|v| v.saturating_add(geo.y));
        let last = geo.last.map(|v| v.saturating_add(geo.y));
        if let Some(p) = self.frames.last_mut() {
            p.flow = pflow;
            if !fin.through {
                if p.first.is_none() {
                    p.first = first;
                }
                if last.is_some() {
                    p.last = last;
                }
            }
        }
    }

    fn exit(&mut self, b: BoxId) {
        match role(self.tree.class(b)) {
            Role::Root => {
                self.lines(b);
                self.frames.pop();
            }
            Role::Flow => {
                if matches!(self.tree.class(b), Class::Replaced { .. }) {
                    let Some(g) = self.geo.get(b).cloned() else {
                        return;
                    };
                    if let Some(p) = self.frames.last_mut() {
                        p.flow = exit(
                            p.flow,
                            Exited::Placed {
                                bottom: g.y.saturating_add(g.height),
                                pending: Collapsed::of(g.margin.bottom),
                            },
                        );
                    }
                } else {
                    self.exit_container(b, true);
                }
            }
            Role::Atomic => {
                if !matches!(self.tree.class(b), Class::Replaced { .. }) {
                    self.exit_container(b, false);
                    // §10.8.1: an inline block whose `overflow` is not
                    // `visible` has no baseline here (its bottom margin edge
                    // is used).
                    let s = self.style(b);
                    if (s.overflow_x != Overflow::Visible || s.overflow_y != Overflow::Visible)
                        && let Some(g) = self.geo_mut(b)
                    {
                        g.last = None;
                    }
                }
            }
            Role::Inline | Role::Marker | Role::Column => {}
        }
    }
}

/// The style used when a box has none (never reached: `box_styles` gives
/// every box one).
fn unreachable_style() -> &'static ComputedStyle {
    static INITIAL: std::sync::OnceLock<ComputedStyle> = std::sync::OnceLock::new();
    INITIAL.get_or_init(ComputedStyle::initial)
}

/// The document element of `arena`, and its body element (the Quirks Mode
/// Standard's "the document's body element": "the first child of the
/// document element that is a body element, if there is one, and the
/// document element is an html element").
fn root_and_body(arena: &Arena) -> (Option<usize>, Option<usize>) {
    if arena.is_empty() {
        return (None, None);
    }
    let root = arena
        .children(0)
        .iter()
        .copied()
        .find(|&c| matches!(arena.kind(c), ExecKind::Element { .. }));
    let body = root
        .filter(|&r| is_html(arena, Some(r), "html"))
        .and_then(|r| {
            arena
                .children(r)
                .iter()
                .copied()
                .find(|&c| is_html(arena, Some(c), "body"))
        });
    (root, body)
}

/// The mode of the document in `arena`.
pub fn mode(arena: &Arena) -> Mode {
    if arena.is_empty() {
        return Mode::NoQuirks;
    }
    match arena.kind(0) {
        ExecKind::Document {
            mode: DocumentMode::Quirks,
            ..
        } => Mode::Quirks,
        ExecKind::Document {
            mode: DocumentMode::LimitedQuirks,
            ..
        } => Mode::LimitedQuirks,
        _ => Mode::NoQuirks,
    }
}

/// Lays out `tree` (`mod.rs`'s pipeline).
pub fn run(
    tree: &BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    fonts: &impl TextFns,
    viewport: Viewport,
) -> FragmentTree {
    let n = tree.boxes.len();
    let styles = box_styles(tree, styles);
    let mut ifcs: HashMap<BoxId, Ifc> = HashMap::new();
    for b in 0..n {
        if role(tree.class(b)) != Role::Inline
            && has_flow(tree.class(b))
            && has_inline_content(tree, b)
        {
            ifcs.insert(b, prepare(tree, &styles, fonts, b));
        }
    }
    let role_of = |b: BoxId| role(tree.class(b));
    let intrinsic = sizes(tree, &styles, &ifcs, &role_of, fonts, arena);
    let (root_node, body_node) = root_and_body(arena);
    let first_box = |node: Option<usize>| {
        node.and_then(|nd| tree.boxes.iter().position(|b| b.node == Some(nd)))
    };
    let root_box = first_box(root_node);
    let html = root_box.filter(|&b| is_html(arena, tree.get(b).and_then(|x| x.node), "html"));
    let body = first_box(body_node).filter(|&b| tree.class(b).is_block_level());
    let mode = mode(arena);
    let html_style = root_box.and_then(|h| styles.get(h));
    let body_propagates = html_style
        .is_some_and(|s| s.overflow_x == Overflow::Visible && s.overflow_y == Overflow::Visible);
    // §3.6 and §3.7: the `html` element's content box height as §3.6 makes
    // it at least, when its `height` is `auto`.
    let html_fill = html.and_then(|h| {
        let s = styles.get(h)?;
        let quirky = mode == Mode::Quirks;
        let vw = viewport.width;
        let definite = size_opt(s.height, Some(viewport.height));
        let (border, padding) = edges(s, vw);
        let margins = size(s.margin[0], vw)
            .unwrap_or(0)
            .saturating_add(size(s.margin[2], vw).unwrap_or(0));
        let bp = border.vertical().saturating_add(padding.vertical());
        match definite {
            Some(d) => Some(d),
            None if quirky => Some(viewport.height.saturating_sub(margins).saturating_sub(bp)),
            None => None,
        }
    });
    let mut w = Walk {
        tree,
        arena,
        fonts,
        mode,
        viewport,
        styles,
        ifcs,
        intrinsic,
        geo: vec![Geo::default(); n],
        frames: Vec::new(),
        tasks: vec![Task::Enter(BoxTree::ROOT)],
        lines: Vec::new(),
        line_origin: Vec::new(),
        root_box,
        html,
        body,
        html_fill,
        body_propagates,
    };
    // Each box is entered at most once and exited at most once.
    for _ in 0..n.saturating_mul(2).saturating_add(2) {
        let Some(task) = w.tasks.pop() else { break };
        match task {
            Task::Enter(b) => match role(tree.class(b)) {
                Role::Root => w.enter_root(b),
                Role::Flow => w.enter_flow(b),
                Role::Atomic => w.enter_atomic(b),
                Role::Inline | Role::Marker | Role::Column => {}
            },
            Task::Exit(b) => w.exit(b),
        }
    }
    w.finish_tree(viewport)
}

impl<F: TextFns> Walk<'_, F> {
    /// Positions made absolute (`mod.rs`'s step 5), and the fragment tree.
    fn finish_tree(self, viewport: Viewport) -> FragmentTree {
        let n = self.tree.boxes.len();
        let mut boxes: Vec<Option<BoxFragment>> = vec![None; n];
        // Each laid-out box's content box origin, in document coordinates.
        let mut origin: Vec<(i32, i32)> = vec![(0, 0); n];
        let vp = Rect {
            x: 0,
            y: 0,
            width: viewport.width.max(0),
            height: viewport.height.max(0),
        };
        let mut extent = vp;
        // A box's positioning parent is an ancestor, so a smaller id.
        for b in 0..n {
            let Some(g) = self.geo.get(b) else { continue };
            if !g.laid {
                continue;
            }
            let (ox, oy) = g
                .parent
                .and_then(|p| origin.get(p).copied())
                .unwrap_or((0, 0));
            let border_box = Rect {
                x: ox.saturating_add(g.x),
                y: oy.saturating_add(g.y),
                width: g.width.max(0),
                height: g.height.max(0),
            };
            if let Some(o) = origin.get_mut(b) {
                *o = (
                    border_box
                        .x
                        .saturating_add(g.border.left)
                        .saturating_add(g.padding.left),
                    border_box
                        .y
                        .saturating_add(g.border.top)
                        .saturating_add(g.padding.top),
                );
            }
            extent = union(extent, border_box);
            if let Some(slot) = boxes.get_mut(b) {
                *slot = Some(BoxFragment {
                    border_box,
                    margin: g.margin,
                    border: g.border,
                    padding: g.padding,
                    first_baseline: g.first.map(|v| border_box.y.saturating_add(v)),
                    last_baseline: g.last.map(|v| border_box.y.saturating_add(v)),
                    lines: g.lines.clone(),
                });
            }
        }
        let mut lines = self.lines;
        for (line, &o) in lines.iter_mut().zip(&self.line_origin) {
            let (ox, oy) = origin.get(o).copied().unwrap_or((0, 0));
            line.rect.x = line.rect.x.saturating_add(ox);
            line.rect.y = line.rect.y.saturating_add(oy);
            line.baseline = line.baseline.saturating_add(oy);
            for item in &mut line.items {
                match item {
                    LineItem::Text(r) => {
                        r.x = r.x.saturating_add(ox);
                        r.baseline = r.baseline.saturating_add(oy);
                    }
                    LineItem::Inline(p) => {
                        p.rect.x = p.rect.x.saturating_add(ox);
                        p.rect.y = p.rect.y.saturating_add(oy);
                    }
                    LineItem::Atomic(_) => {}
                }
            }
            extent = union(extent, line.rect);
        }
        FragmentTree {
            boxes,
            lines,
            nodes: self.tree.boxes.iter().map(|b| b.node).collect(),
            viewport: vp,
            extent,
        }
    }
}
