//! The paint walk: CSS 2.1 Appendix E.2's painting order for the root
//! stacking context, the only one the subset makes (phase-5.md item 5.16).
//!
//! Sources: CSS 2.1 Appendix E.2 (steps numbered as in `mod.rs`), §14.2,
//! §8.5, §11.1.1, §11.2, §16.3.1, §17.5.1, §17.6.1; HTML §4.6.2 and §4.6.4.
//!
//! Modelling choices (with `mod.rs`'s):
//!
//! - **One loop over an explicit stack of tasks** ([`Task`]); nothing
//!   recurses, so a document of any depth paints. A stacking context's
//!   steps 2 and 4 are the `Back` tasks of its block-level boxes in tree
//!   order, its step 7 the `Fore` tasks; an atomic inline met in a line
//!   (7.2.1.5) pushes the rest of its line, then its own `Fore` and `Back`
//!   tasks, so it is painted whole before the line goes on.
//! - **A box's children in the walk** are its block-level, table and cell
//!   descendants down to the next block container with inline content;
//!   inline boxes and text runs are painted from their line boxes, and an
//!   atomic inline from the line it sits on.
//! - **A clip** surrounds a box's descendants in each pass: entered after
//!   the box's own background and borders, left after its last descendant
//!   (a `BackExit` or `ForeExit` task).

use std::collections::HashMap;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{ComputedStyle, Overflow, Visibility};
use clazel_style::cascade::hints::{attribute, is_html};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;

use super::decor::{line_rect, propagate};
use super::geometry::{border_rects, clamp_scale, fine, premultiply, snap_rect, transparent};
use super::state::{
    ClipChange, Clips, Decor, DeviceRect, DisplayList, HitRegion, Item, Line, PlacedGlyph, TextItem,
};
use crate::boxes::replaced::string;
use crate::boxes::{BoxId, BoxKind, BoxTree, Class, StyleFns};
use crate::flow::TextFns;
use crate::flow::block::{Mode, mode};
use crate::flow::fragment::{FragmentTree, GlyphRun, InlinePiece, LineItem, Rect, Sides};
use crate::flow::style::box_styles;

/// The UA's canvas colour (E.2: "given a UA-defined color"): opaque white.
const CANVAS: [u8; 4] = [255, 255, 255, 255];

/// A task of the walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Task {
    /// E.2 steps 2 and 4 for a box; `root` when it is the stacking
    /// context's own box (an atomic inline is otherwise skipped here).
    Back { b: BoxId, root: bool },
    /// The end of a box's descendants in steps 2 and 4: its clip ends.
    BackExit,
    /// E.2 step 7 for a box.
    Fore { b: BoxId, root: bool },
    /// The end of a box's descendants in step 7.
    ForeExit,
    /// Step 7.2: line boxes `line .. end`, from item `item` of the first.
    Lines {
        line: usize,
        end: usize,
        item: usize,
    },
}

/// Whether a box of class `c` is an atomic inline (E.2 7.2.1.5 and
/// 7.2.1.6).
fn atomic(c: Class) -> bool {
    matches!(
        c,
        Class::InlineBlock
            | Class::Replaced { inline: true }
            | Class::TableWrapper { inline: true }
    )
}

/// Whether a box of class `c` is visited by the walk as a box (not an
/// inline box, a text run or a marker, which lines paint).
fn walked(c: Class) -> bool {
    !matches!(c, Class::Inline | Class::Text { .. } | Class::Marker)
}

struct Walk<'a, F: TextFns> {
    frags: &'a FragmentTree,
    tree: &'a BoxTree,
    arena: &'a Arena,
    fonts: &'a F,
    styles: Vec<ComputedStyle>,
    decor: Vec<Decor>,
    link: Vec<Option<usize>>,
    urls: HashMap<usize, Option<String>>,
    base: Option<&'a ParsedUrl>,
    scale: u32,
    clips: Clips,
    /// The clip in force before each clip on the stack.
    outer: Vec<Option<DeviceRect>>,
    /// Boxes whose `overflow` clips their content.
    clipping: Vec<bool>,
    /// A box whose background went to the canvas (§14.2).
    canvas_box: Option<BoxId>,
    root_box: Option<BoxId>,
    out: DisplayList,
}

impl<F: TextFns> Walk<'_, F> {
    fn style(&self, b: BoxId) -> Option<&ComputedStyle> {
        self.styles.get(b)
    }

    fn visible(&self, b: BoxId) -> bool {
        self.style(b)
            .is_some_and(|s| s.visibility == Visibility::Visible)
    }

    fn fill(&mut self, r: Rect, rgba: [u8; 4]) {
        if transparent(rgba) {
            return;
        }
        let rect = snap_rect(r, self.scale);
        if rect.is_empty() {
            return;
        }
        self.out.items.push(Item::Fill {
            rect,
            colour: premultiply(rgba),
        });
    }

    fn change(&mut self, c: ClipChange) {
        if c.pop {
            self.out.items.push(Item::PopClip);
        }
        if let Some(rect) = c.push {
            self.out.items.push(Item::PushClip { rect });
        }
    }

    /// §11.1: box `b` clips its descendants "to its padding edge".
    fn clip_enter(&mut self, b: BoxId) {
        let Some(f) = self.frags.fragment(b) else {
            return;
        };
        let rect = snap_rect(f.padding_box(), self.scale);
        self.outer.push(self.clips.current);
        let (next, change) = self.clips.enter(rect);
        self.clips = next;
        self.change(change);
    }

    fn clip_leave(&mut self) {
        let outer = self.outer.pop().flatten();
        let (next, change) = self.clips.leave(outer);
        self.clips = next;
        self.change(change);
    }

    /// A hit region for box `b`'s rectangle `r`, if `b` is in a link.
    fn hit(&mut self, b: BoxId, r: Rect) {
        let Some(node) = self.link.get(b).copied().flatten() else {
            return;
        };
        let rect = snap_rect(r, self.scale);
        if rect.is_empty() {
            return;
        }
        let (arena, base) = (self.arena, self.base);
        let url = self
            .urls
            .entry(node)
            .or_insert_with(|| resolve(arena, node, base))
            .clone();
        self.out.hits.push(HitRegion { rect, node, url });
    }

    /// E.2 2.1/4.1 to 4.3 for box `b`: "background color of element",
    /// "border of element", and its hit region.
    fn background_and_border(&mut self, b: BoxId) {
        let Some(f) = self.frags.fragment(b).cloned() else {
            return;
        };
        if !self.visible(b) {
            return;
        }
        let Some(s) = self.style(b) else { return };
        let (bg, colours) = (s.background_color, s.border_color);
        // §14.2: the root element's background is the canvas's ("The root
        // element does not paint this background again"), and so is a
        // `body`'s whose background went there.
        if Some(b) != self.root_box && Some(b) != self.canvas_box {
            self.fill(f.border_box, bg);
        }
        let strips = border_rects(f.border_box, f.border);
        for (r, c) in strips
            .into_iter()
            .zip([colours[0], colours[1], colours[2], colours[3]])
        {
            self.fill(r, c);
        }
        self.hit(b, f.border_box);
    }

    /// E.2 step 4 for a table box `t`: "table backgrounds", "column group
    /// backgrounds", "column backgrounds", "row group backgrounds", "row
    /// backgrounds", "cell backgrounds", "all table borders (in tree order
    /// for separated borders)" (`mod.rs`'s "Tables").
    fn table(&mut self, t: BoxId) {
        let tree = self.tree;
        let mut cells: Vec<BoxId> = Vec::new();
        let mut groups: Vec<BoxId> = Vec::new();
        let mut columns: Vec<BoxId> = Vec::new();
        for &c in tree.children(t) {
            match tree.class(c) {
                Class::RowGroup => {
                    for &r in tree.children(c) {
                        cells.extend(tree.children(r).iter().copied());
                    }
                }
                Class::Row => cells.extend(tree.children(c).iter().copied()),
                Class::ColumnGroup => {
                    groups.push(c);
                    columns.extend(tree.children(c).iter().copied());
                }
                Class::Column => columns.push(c),
                _ => {}
            }
        }
        cells.retain(|&c| tree.class(c) == Class::Cell);
        // "table backgrounds".
        if let Some(f) = self.frags.fragment(t).cloned()
            && self.visible(t)
            && let Some(s) = self.style(t)
        {
            let bg = s.background_color;
            self.fill(f.border_box, bg);
        }
        let rect_of = |b: BoxId| self.frags.fragment(b).map(|f| f.border_box);
        // The column (group) a cell starts in: the one whose span holds the
        // cell's left edge.
        let column_of = |tracks: &[BoxId], cell: Rect| -> Option<BoxId> {
            tracks
                .iter()
                .copied()
                .find(|&k| rect_of(k).is_some_and(|r| r.x <= cell.x && cell.x < r.right()))
        };
        let layers: [&dyn Fn(BoxId, Rect) -> Option<BoxId>; 4] = [
            &|_, r| column_of(&groups, r),
            &|_, r| column_of(&columns, r),
            &|c, _| {
                let row = tree.get(c).and_then(|x| x.parent)?;
                tree.get(row)
                    .and_then(|x| x.parent)
                    .filter(|&g| tree.class(g) == Class::RowGroup)
            },
            &|c, _| tree.get(c).and_then(|x| x.parent),
        ];
        let mut fills: Vec<(Rect, [u8; 4])> = Vec::new();
        for layer in layers {
            for &c in &cells {
                let Some(r) = rect_of(c) else { continue };
                if let Some(k) = layer(c, r)
                    && self.visible(k)
                    && let Some(s) = self.style(k)
                {
                    fills.push((r, s.background_color));
                }
            }
        }
        for (r, c) in fills {
            self.fill(r, c);
        }
        // "cell backgrounds".
        for &c in &cells {
            if let (Some(r), true) = (rect_of(c), self.visible(c))
                && let Some(s) = self.style(c)
            {
                let bg = s.background_color;
                self.fill(r, bg);
            }
        }
        // "all table borders (in tree order for separated borders)".
        for b in std::iter::once(t).chain(cells.iter().copied()) {
            let Some(f) = self.frags.fragment(b).cloned() else {
                continue;
            };
            if self.visible(b)
                && let Some(s) = self.style(b)
            {
                let colours = s.border_color;
                for (r, c) in border_rects(f.border_box, f.border)
                    .into_iter()
                    .zip(colours)
                {
                    self.fill(r, c);
                }
            }
            self.hit(b, f.border_box);
        }
    }

    /// The children of box `b` the walk visits, in tree order.
    fn walked_children(&self, b: BoxId) -> Vec<BoxId> {
        if self.frags.fragment(b).is_some_and(|f| !f.lines.is_empty()) {
            // A block container with inline content: its children are its
            // lines' (step 7.2).
            return Vec::new();
        }
        self.tree
            .children(b)
            .iter()
            .copied()
            .filter(|&c| walked(self.tree.class(c)))
            .collect()
    }

    /// `Back` for box `b` (E.2 steps 2 and 4).
    fn back(&mut self, b: BoxId, root: bool, tasks: &mut Vec<Task>) {
        let class = self.tree.class(b);
        if !root && atomic(class) {
            return;
        }
        match class {
            Class::Table { .. } => self.table(b),
            // A table's layers and cells are its own (`table`).
            Class::Cell | Class::Row | Class::RowGroup | Class::Column | Class::ColumnGroup => {}
            Class::Root => {}
            _ => self.background_and_border(b),
        }
        let clips = self.clipping.get(b).copied().unwrap_or(false);
        if clips {
            self.clip_enter(b);
            tasks.push(Task::BackExit);
        }
        let children = self.walked_children(b);
        tasks.extend(
            children
                .into_iter()
                .rev()
                .map(|c| Task::Back { b: c, root: false }),
        );
    }

    /// `Fore` for box `b` (E.2 step 7: "first for the element, then for all
    /// its in-flow, non-positioned, block-level descendants in tree
    /// order").
    fn fore(&mut self, b: BoxId, root: bool, tasks: &mut Vec<Task>) {
        let class = self.tree.class(b);
        if !root && atomic(class) {
            return;
        }
        // 7.1: "If the element is a block-level replaced element, then: the
        // replaced content, atomically": nothing in this phase.
        if matches!(class, Class::Replaced { .. }) {
            return;
        }
        let clips = self.clipping.get(b).copied().unwrap_or(false);
        if clips {
            self.clip_enter(b);
            tasks.push(Task::ForeExit);
        }
        let children = self.walked_children(b);
        tasks.extend(
            children
                .into_iter()
                .rev()
                .map(|c| Task::Fore { b: c, root: false }),
        );
        // A list item's marker (its first child) has a line of its own.
        if let Some(&m) = self.tree.children(b).first()
            && self.tree.class(m) == Class::Marker
            && let Some(f) = self.frags.fragment(m)
            && !f.lines.is_empty()
        {
            let (line, end) = (f.lines.start, f.lines.end);
            self.lines(line, end, 0, tasks);
        }
        if let Some(f) = self.frags.fragment(b)
            && !f.lines.is_empty()
        {
            tasks.push(Task::Lines {
                line: f.lines.start,
                end: f.lines.end,
                item: 0,
            });
        }
    }

    /// Step 7.2 for lines `line .. end`, from item `item`: paints until an
    /// atomic inline, which it schedules with the rest after it.
    fn lines(&mut self, line: usize, end: usize, item: usize, tasks: &mut Vec<Task>) {
        let mut l = line;
        let mut i = item;
        while l < end {
            let Some(lb) = self.frags.lines.get(l) else {
                return;
            };
            let Some(it) = lb.items.get(i) else {
                l = l.saturating_add(1);
                i = 0;
                continue;
            };
            i = i.saturating_add(1);
            match it {
                LineItem::Inline(p) => self.piece(p),
                LineItem::Text(r) => self.run(r),
                LineItem::Atomic(a) => {
                    // 7.2.1.5: "treat the element as if it created a new
                    // stacking context"; 7.2.1.6: "the replaced content,
                    // atomically". The line goes on after it.
                    tasks.push(Task::Lines {
                        line: l,
                        end,
                        item: i,
                    });
                    tasks.push(Task::Fore { b: *a, root: true });
                    tasks.push(Task::Back { b: *a, root: true });
                    return;
                }
            }
        }
    }

    /// 7.2.1.1 to 7.2.1.3 for a piece of an inline box: its background and
    /// borders over its border area on this line (`mod.rs`).
    fn piece(&mut self, p: &InlinePiece) {
        let Some(f) = self.frags.fragment(p.inline).cloned() else {
            return;
        };
        let (pd, bd) = (f.padding, f.border);
        let pad = Rect {
            x: p.rect.x,
            y: p.rect.y.saturating_sub(pd.top),
            width: p.rect.width,
            height: p
                .rect
                .height
                .saturating_add(pd.top)
                .saturating_add(pd.bottom),
        };
        let edges = Sides {
            top: bd.top,
            right: if p.end_edge { bd.right } else { 0 },
            bottom: bd.bottom,
            left: if p.start_edge { bd.left } else { 0 },
        };
        let border_box = pad.outset(&edges);
        self.hit(p.inline, border_box);
        if !self.visible(p.inline) {
            return;
        }
        let Some(s) = self.style(p.inline) else {
            return;
        };
        let (bg, colours) = (s.background_color, s.border_color);
        self.fill(border_box, bg);
        for (r, c) in border_rects(border_box, edges).into_iter().zip(colours) {
            self.fill(r, c);
        }
    }

    /// 7.2.1.4.1 for a run of text: "any underlining", "any overlining",
    /// "the text", "any line-through".
    fn run(&mut self, r: &GlyphRun) {
        if r.glyphs.is_empty() || !self.visible(r.source) {
            return;
        }
        let Some(style) = self.style(r.source).cloned() else {
            return;
        };
        let end = r
            .glyphs
            .iter()
            .map(|g| g.x.saturating_add(g.advance))
            .max()
            .unwrap_or(0)
            .max(0);
        let decor = self.decor.get(r.source).copied().unwrap_or_default();
        let m = self.fonts.metrics(&style);
        let deco = |w: &mut Self, kind: Line, colour: Option<[u8; 4]>| {
            if let Some(c) = colour {
                let rect = line_rect(kind, r.baseline, &m, r.x, end);
                w.fill_line(rect, c);
            }
        };
        deco(self, Line::Underline, decor.underline);
        deco(self, Line::Overline, decor.overline);
        let size = r.size.max(0);
        let bounds = snap_rect(
            Rect {
                x: r.x.saturating_sub(size),
                y: r.baseline.saturating_sub(size.saturating_mul(2)),
                width: end.saturating_add(size.saturating_mul(2)),
                height: size.saturating_mul(3),
            },
            self.scale,
        );
        let scale = self.scale;
        let glyphs = r
            .glyphs
            .iter()
            .map(|g| PlacedGlyph {
                id: g.id,
                x: fine(r.x.saturating_add(g.x), scale),
                y: fine(r.baseline.saturating_add(g.y), scale),
            })
            .collect();
        if !transparent(style.color) {
            self.out.items.push(Item::Text {
                bounds,
                run: TextItem {
                    face: r.face,
                    size: fine(r.size, scale),
                    colour: premultiply(style.color),
                    glyphs,
                },
            });
        }
        deco(self, Line::LineThrough, decor.line_through);
    }

    /// A decoration line, at least one device pixel thick (`mod.rs`).
    fn fill_line(&mut self, r: Rect, rgba: [u8; 4]) {
        if transparent(rgba) {
            return;
        }
        let mut rect = snap_rect(r, self.scale);
        if rect.width == 0 {
            return;
        }
        if rect.height == 0 {
            rect.height = 1;
        }
        self.out.items.push(Item::Fill {
            rect,
            colour: premultiply(rgba),
        });
    }
}

/// HTML §4.6.4: "the result of encoding-parsing a URL given subject's href
/// attribute value, relative to subject's node document", serialized, or
/// `None` on failure (`mod.rs`: UTF-8).
fn resolve(arena: &Arena, node: usize, base: Option<&ParsedUrl>) -> Option<String> {
    let href = match arena.kind(node) {
        ExecKind::Element { attributes, .. } => attribute(attributes, "href")?,
        _ => return None,
    };
    // The parser takes scalar values only; a DOM string may hold a lone
    // surrogate, which is a failure here.
    if href.iter().any(|&c| char::from_u32(c).is_none()) {
        return None;
    }
    let url = basic_url_parser(href, base)?;
    Some(string(&url.serialize(false)))
}

/// HTML §4.6.2: an `a` or `area` element with an `href` attribute creates
/// a hyperlink.
fn hyperlink(arena: &Arena, node: usize) -> bool {
    if node >= arena.len() || !(is_html(arena, node, "a") || is_html(arena, node, "area")) {
        return false;
    }
    matches!(arena.kind(node), ExecKind::Element { attributes, .. } if attribute(attributes, "href").is_some())
}

/// The document element's node and its body element's (the Quirks Mode
/// Standard's "the document's body element"), as 5.14 finds them.
fn root_and_body(arena: &Arena) -> (Option<usize>, Option<usize>) {
    if arena.is_empty() {
        return (None, None);
    }
    let root = arena
        .children(0)
        .iter()
        .copied()
        .find(|&c| matches!(arena.kind(c), ExecKind::Element { .. }));
    let body = root.filter(|&r| is_html(arena, r, "html")).and_then(|r| {
        arena
            .children(r)
            .iter()
            .copied()
            .find(|&c| is_html(arena, c, "body"))
    });
    (root, body)
}

/// The display list of fragment tree `frags` of box tree `tree` (built
/// from `arena` with computed style `styles`, laid out in fonts `fonts`),
/// with links resolved against base URL `base`, at `scale` device pixels per
/// CSS pixel (the module's pipeline).
pub fn paint(
    frags: &FragmentTree,
    tree: &BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    fonts: &impl TextFns,
    base: Option<&ParsedUrl>,
    scale: u32,
) -> DisplayList {
    let n = tree.boxes.len();
    let styles = box_styles(tree, styles);
    let quirks = mode(arena) == Mode::Quirks;
    // Decorations and links, top down (ids are in tree order).
    let mut decor = vec![Decor::default(); n];
    let mut link: Vec<Option<usize>> = vec![None; n];
    for b in 0..n {
        let Some(lb) = tree.get(b) else { continue };
        let parent = lb.parent;
        let class = lb.kind.class();
        let cut = atomic(class) || (quirks && matches!(class, Class::TableWrapper { .. }));
        let from = parent
            .and_then(|p| decor.get(p).copied())
            .unwrap_or_default();
        let d = match styles.get(b) {
            Some(s) => propagate(from, s.text_decoration_line, s.text_decoration_color, cut),
            None => from,
        };
        if let Some(slot) = decor.get_mut(b) {
            *slot = d;
        }
        let own = lb
            .node
            .filter(|&nd| !matches!(lb.kind, BoxKind::Text(_)) && hyperlink(arena, nd));
        let l = own.or_else(|| parent.and_then(|p| link.get(p).copied().flatten()));
        if let Some(slot) = link.get_mut(b) {
            *slot = l;
        }
    }
    let (root_node, body_node) = root_and_body(arena);
    let first_box = |node: Option<usize>| {
        node.and_then(|nd| tree.boxes.iter().position(|b| b.node == Some(nd)))
    };
    let root_box = first_box(root_node);
    let body_box = first_box(body_node).filter(|&b| tree.class(b).is_block_level());
    let html = root_box.filter(|&b| {
        is_html(
            arena,
            tree.get(b).and_then(|x| x.node).unwrap_or(usize::MAX),
            "html",
        )
    });
    let bg = |b: Option<BoxId>| b.and_then(|b| styles.get(b)).map(|s| s.background_color);
    // §14.2: the canvas takes the root's background, or for an `html`
    // root with a transparent one, its `body`'s.
    let (canvas, canvas_box) = match bg(root_box) {
        Some(c) if !transparent(c) => (c, None),
        _ => match bg(body_box) {
            Some(c) if html.is_some() && !transparent(c) => (c, body_box),
            _ => (CANVAS, None),
        },
    };
    // §11.1.1: the root's `overflow`, and the body's when the root's is
    // `visible`, go to the viewport.
    let root_visible = root_box
        .and_then(|b| styles.get(b))
        .is_none_or(|s| s.overflow_x == Overflow::Visible && s.overflow_y == Overflow::Visible);
    let clipping: Vec<bool> = (0..n)
        .map(|b| {
            let Some(s) = styles.get(b) else { return false };
            let clips = s.overflow_x != Overflow::Visible || s.overflow_y != Overflow::Visible;
            let propagated =
                Some(b) == root_box || (Some(b) == body_box && html.is_some() && root_visible);
            clips && !propagated && tree.class(b).is_block_container()
        })
        .collect();
    let scale = clamp_scale(scale);
    let mut w = Walk {
        frags,
        tree,
        arena,
        fonts,
        styles,
        decor,
        link,
        urls: HashMap::new(),
        base,
        scale,
        clips: Clips::NONE,
        outer: Vec::new(),
        clipping,
        canvas_box,
        root_box,
        out: DisplayList {
            items: Vec::new(),
            hits: Vec::new(),
            scale,
        },
    };
    // Step 1: "background color of element over the entire canvas".
    w.fill(frags.extent, canvas);
    let mut tasks: Vec<Task> = vec![
        Task::Fore {
            b: BoxTree::ROOT,
            root: true,
        },
        Task::Back {
            b: BoxTree::ROOT,
            root: true,
        },
    ];
    // Each box is visited at most twice per pass, and each line item once.
    let bound = n
        .saturating_mul(6)
        .saturating_add(
            frags
                .lines
                .iter()
                .map(|l| l.items.len().saturating_add(1))
                .sum::<usize>(),
        )
        .saturating_add(4);
    for _ in 0..bound {
        let Some(t) = tasks.pop() else { break };
        match t {
            Task::Back { b, root } => w.back(b, root, &mut tasks),
            Task::Fore { b, root } => w.fore(b, root, &mut tasks),
            Task::BackExit | Task::ForeExit => w.clip_leave(),
            Task::Lines { line, end, item } => w.lines(line, end, item, &mut tasks),
        }
    }
    w.out
}
