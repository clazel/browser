//! Inline formatting contexts and line boxes (CSS 2.1 §9.4.2, §10.8,
//! §16.1, §16.2) with the Quirks Mode Standard's §3.3 and §3.4 (phase-5.md
//! item 5.14).
//!
//! Sources: CSS 2.1 (W3C Recommendation, 7 June 2011), §9.4.2 "Inline
//! formatting contexts", §10.3.1 (inline boxes' horizontal margins), §10.8
//! "Line height calculations" (its numbered list: 1. each box's height, 2.
//! vertical alignment, 3. the line box's height) and §10.8.1, §16.1
//! `text-indent`, §16.2 `text-align`; CSS Text 3 (CRD of 14 August 2026)
//! §4.1.2 Phase II and §5 through item 5.12's [`crate::text`], and §7.1†
//! (overflowing lines are start-aligned); the Quirks Mode Standard (commit
//! `5a06deb5`) §3.3 and §3.4.
//!
//! Modelling choices:
//!
//! - **The content of a context** is gathered as item 5.13 gathered it for
//!   Phase I: its text runs' units (Phase I's output, which the box tree
//!   keeps) and one unit (U+FFFC) per atomic inline, whose breaking is
//!   governed by its parent box's `white-space`, `word-break` and
//!   `overflow-wrap` (CSS Text 3 §5.5). Wrap opportunities are item 5.12's
//!   `text::wrap::opportunities` over the whole context.
//! - **Each text run is shaped once**, as a whole ([`super::fonts`]); each
//!   unit's advance is the sum of its glyphs'. A collapsible space is shaped
//!   as U+0020. A forced break, a preserved tab and the default ignorable
//!   characters U+00AD, U+200B to U+200D, U+2060 and U+FEFF draw no glyph and
//!   have no advance (a tab's advance is CSS Text 3 §4.2's, from its pen
//!   position): fonts map few of them, and `.notdef` would draw a box.
//! - **Inline boxes' edges**: an inline box's start edge (its left margin,
//!   border and padding, §10.3.1: an `auto` margin is 0) goes before its
//!   first unit, if the box is its own first fragment (item 5.13's
//!   `Fragment`), and its end edge after its last unit, if it is its last;
//!   for line breaking, a start edge is part of the unit after it and an end
//!   edge of the unit before it, so an edge is never separated from the
//!   content beside it. An inline box with no unit (an empty element) takes
//!   no width and does not affect line heights (CSS 2.1 §10.8 says "Empty
//!   inline elements generate empty inline boxes, but these boxes still have
//!   margins, padding, borders and a line height"; listed). An edge next to a
//!   unit that Phase II removes at a line's start or end is dropped with it.
//! - **Choosing lines** is item 5.12's `fit_step` (first fit), driven here
//!   with each line's own available width: the first line's is narrower by
//!   the text indent.
//! - **`text-indent`** (§16.1) applies to the first line of a block
//!   container that is an element, or an anonymous block that is its
//!   parent's first child ("the first line of an anonymous block box is only
//!   affected if it is the first child of its parent element"); CSS Text 3's
//!   `each-line` adds the lines after a forced break and `hanging` inverts
//!   which lines are indented. A percentage is of the block container's own
//!   content width.
//! - **Alignment** (§16.2): `justify` is drawn as `left` (the plan; §16.2
//!   allows it), `start` is `left` and `end` `right`. The content measured is
//!   from the line's start to the end of its content without what hangs. A
//!   line whose content is wider than the line box is start-aligned (CSS Text
//!   3 §7.1†: "the contents are start-aligned: any content that doesn't fit
//!   overflows the line box's end edge").
//! - **A line box is empty** (§9.4.2: "Line boxes that contain no text, no
//!   preserved white space, no inline elements with non-zero margins,
//!   padding, or borders, and no other in-flow content … and do not end with
//!   a preserved newline must be treated as zero-height line boxes") when no
//!   unit Phase II keeps is a character, a preserved space or tab, an other
//!   space separator or an atomic inline, no edge with a non-zero width is
//!   on it, and it does not end in a forced break unit. It has height zero,
//!   and is "treated as not existing" for margin collapsing and baselines.
//! - **Vertical alignment** (§10.8.1): every box's baseline is found from its
//!   parent's (the root inline box's is zero), in tree order. `sub` lowers a
//!   box by a fifth of its parent's font size and `super` raises it by a
//!   third ("the proper position for subscripts", which CSS 2.1 leaves to the
//!   user agent). `top` and `bottom` align each aligned subtree, with its own
//!   extent, after the others are placed: first the `top` ones, which may
//!   push the line's bottom down, then the `bottom` ones, which may push its
//!   top up (CSS 2.1 leaves the choice open when such boxes are tall; this
//!   one keeps the strut where the other boxes put it).
//! - **The strut and the anonymous inline boxes** (§10.8.1, §9.2.2.1): the
//!   root inline box has the container's font and line height and is always
//!   on a line that is not empty; text directly in the container is in it.
//!   In quirks and limited-quirks mode, §3.4 removes the strut ("the element's
//!   line-height must be ignored for the purpose of calculating the minimal
//!   height of line boxes"), so the root inline box counts only on a line
//!   where it holds text of its own (its anonymous inline boxes, which
//!   inherit the same line height); and §3.3 gives an inline box whose left
//!   and right borders and padding are zero, and which holds no text on the
//!   line or only collapsible spaces, "a line-height of zero": such a box is
//!   left out of the line's height. An atomic inline is never text.
//! - **An atomic inline's baseline** is its last line box's baseline for an
//!   inline block whose `overflow` is `visible` and which has one; otherwise
//!   its bottom margin edge (§10.8.1: "If the box does not have a baseline,
//!   align the bottom margin edge with the parent's baseline"), which is the
//!   case for every replaced element.

use std::collections::HashMap;
use std::ops::Range;

use clazel_style::cascade::computed::{ComputedStyle, VerticalAlign};

use super::fonts::{FontMetrics, ShapedGlyph, TextFns};
use super::fragment::{Glyph, GlyphRun, InlinePiece, LineBox, LineItem, Rect};
use super::heights::{half_leading, line_height};
use super::length::{half_down, lp, size};
use super::state::{Align, LineExtent, line_align};
use crate::boxes::{BoxId, BoxKind, BoxTree, Class};
use crate::text::collapse::{Kind, Unit};
use crate::text::lines::{initial_tab_size, tab_advance, trim};
use crate::text::state::{Fit, FitState};
use crate::text::wrap::{Wrap, opportunities};
use crate::text::{TextStyle, lines::fit_step};

/// One inline box of a context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineInfo {
    /// The inline box.
    pub id: BoxId,
    /// Its parent inline box in the context (`None`: the root inline box).
    pub parent: Option<usize>,
    /// Its units.
    pub units: Range<usize>,
    /// Its start edge is drawn (its own first fragment).
    pub first: bool,
    /// Its end edge is drawn (its own last fragment).
    pub last: bool,
}

/// One inline formatting context, prepared (see the module's modelling
/// choices).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ifc {
    /// Its block container.
    pub container: BoxId,
    /// Its units, in order.
    pub units: Vec<Unit>,
    /// The wrap opportunity after each unit.
    pub wraps: Vec<Wrap>,
    /// The text run or atomic inline each unit belongs to.
    pub owner: Vec<BoxId>,
    /// Each unit's index among its text run's units.
    pub in_run: Vec<usize>,
    /// Each unit's innermost inline box, as an index into `inlines`.
    pub parent: Vec<Option<usize>>,
    /// Each unit's advance (0 for a tab, an atomic inline and what draws
    /// nothing; layout supplies the first two).
    pub advance: Vec<i32>,
    /// Each preserved tab's tab size and half `ch`, else zeros.
    pub tab: Vec<(i32, i32)>,
    /// The glyphs of every text run, in unit order.
    pub glyphs: Vec<ShapedGlyph>,
    /// Each unit's glyphs.
    pub glyph_range: Vec<Range<usize>>,
    /// The inline boxes, in tree order.
    pub inlines: Vec<InlineInfo>,
    /// The atomic inlines, in order.
    pub atomics: Vec<BoxId>,
}

/// Default ignorable characters that draw nothing (the module's modelling
/// choices).
fn draws_nothing(u: &Unit) -> bool {
    matches!(u.kind, Kind::ForcedBreak | Kind::PreservedTab)
        || matches!(
            u.ch,
            '\u{00AD}' | '\u{200B}' | '\u{200C}' | '\u{200D}' | '\u{2060}' | '\u{FEFF}'
        )
}

/// The text style that governs breaking around an atomic inline: its
/// parent box's (item 5.13's choice for Phase I).
fn text_style(s: &ComputedStyle) -> TextStyle {
    TextStyle {
        white_space: s.white_space,
        word_break: s.word_break,
        overflow_wrap: s.overflow_wrap,
    }
}

/// Whether block container `b` of `tree` establishes an inline formatting
/// context: it has an inline-level child and every child is inline-level
/// or a marker (item 5.13 leaves no block container with both).
pub fn has_inline_content(tree: &BoxTree, b: BoxId) -> bool {
    let children = tree.children(b);
    children.iter().any(|&c| tree.class(c).is_inline_level())
        && children.iter().all(|&c| {
            let k = tree.class(c);
            k.is_inline_level() || k == Class::Marker
        })
}

/// Shapes the units `run_units` (indexes into `ifc.units`) of one text run
/// with style `style`, filling their advances and glyphs.
fn shape_run(ifc: &mut Ifc, run_units: &[usize], style: &ComputedStyle, fonts: &impl TextFns) {
    let mut text = String::new();
    let mut starts: Vec<usize> = Vec::with_capacity(run_units.len());
    for &k in run_units {
        starts.push(text.len());
        if let Some(u) = ifc.units.get(k) {
            text.push(u.ch);
        }
    }
    let mut shaped = fonts.shape(style, &text);
    // The unit each glyph draws: the last whose text starts at or before
    // its cluster.
    let unit_of = |cluster: usize| starts.partition_point(|&s| s <= cluster).saturating_sub(1);
    shaped.sort_by_key(|g| unit_of(g.cluster));
    let mut per_unit: Vec<Vec<ShapedGlyph>> = vec![Vec::new(); run_units.len()];
    for g in shaped {
        if let Some(list) = per_unit.get_mut(unit_of(g.cluster)) {
            list.push(g);
        }
    }
    let half_ch = half_down(fonts.metrics(style).average);
    let mut tab_size: Option<i32> = None;
    for (j, &k) in run_units.iter().enumerate() {
        let Some(u) = ifc.units.get(k).copied() else {
            continue;
        };
        let list = per_unit.get_mut(j).map(std::mem::take).unwrap_or_default();
        let start = ifc.glyphs.len();
        let mut advance = 0i32;
        if u.kind == Kind::PreservedTab {
            // §4.2: "a multiple of the advance width of the space character".
            let size = *tab_size.get_or_insert_with(|| {
                let space: i32 = fonts
                    .shape(style, " ")
                    .iter()
                    .fold(0, |a, g| a.saturating_add(g.advance));
                initial_tab_size(space)
            });
            if let Some(t) = ifc.tab.get_mut(k) {
                *t = (size, half_ch);
            }
        } else if !draws_nothing(&u) {
            for g in list {
                advance = advance.saturating_add(g.advance);
                ifc.glyphs.push(g);
            }
        }
        if let Some(a) = ifc.advance.get_mut(k) {
            *a = advance;
        }
        if let Some(r) = ifc.glyph_range.get_mut(k) {
            *r = start..ifc.glyphs.len();
        }
    }
}

/// The inline formatting context of block container `container`: its
/// units in order, gathered through its inline boxes with an explicit
/// stack, and each text run shaped.
pub fn prepare(
    tree: &BoxTree,
    styles: &[ComputedStyle],
    fonts: &impl TextFns,
    container: BoxId,
) -> Ifc {
    let mut ifc = Ifc {
        container,
        units: Vec::new(),
        wraps: Vec::new(),
        owner: Vec::new(),
        in_run: Vec::new(),
        parent: Vec::new(),
        advance: Vec::new(),
        tab: Vec::new(),
        glyphs: Vec::new(),
        glyph_range: Vec::new(),
        inlines: Vec::new(),
        atomics: Vec::new(),
    };
    let mut runs: Vec<(BoxId, Vec<usize>)> = Vec::new();
    // (box, exiting); the stack of open inline boxes (indexes into
    // `ifc.inlines`).
    let mut stack: Vec<(BoxId, bool)> = tree
        .children(container)
        .iter()
        .rev()
        .map(|&c| (c, false))
        .collect();
    let mut open: Vec<usize> = Vec::new();
    // Each box under the container is pushed at most twice.
    let bound = tree.boxes.len().saturating_mul(2).saturating_add(1);
    for _ in 0..bound {
        let Some((b, exiting)) = stack.pop() else {
            break;
        };
        if exiting {
            if let Some(i) = open.pop()
                && let Some(info) = ifc.inlines.get_mut(i)
            {
                info.units.end = ifc.units.len();
            }
            continue;
        }
        let Some(lb) = tree.get(b) else { continue };
        let parent = open.last().copied();
        let push_unit = |ifc: &mut Ifc, u: Unit, in_run: usize| {
            ifc.units.push(u);
            ifc.owner.push(b);
            ifc.in_run.push(in_run);
            ifc.parent.push(parent);
            ifc.advance.push(0);
            ifc.tab.push((0, 0));
            ifc.glyph_range.push(0..0);
        };
        match &lb.kind {
            BoxKind::Text(run) => {
                let mut mine = Vec::with_capacity(run.units.len());
                for (j, u) in run.units.iter().enumerate() {
                    mine.push(ifc.units.len());
                    push_unit(&mut ifc, *u, j);
                }
                runs.push((b, mine));
            }
            BoxKind::Inline(f) => {
                let i = ifc.inlines.len();
                ifc.inlines.push(InlineInfo {
                    id: b,
                    parent,
                    units: ifc.units.len()..ifc.units.len(),
                    first: f.first,
                    last: f.last,
                });
                open.push(i);
                stack.push((b, true));
                stack.extend(tree.children(b).iter().rev().map(|&c| (c, false)));
            }
            _ if lb.kind.class().is_atomic_inline() => {
                let style = lb
                    .parent
                    .and_then(|p| styles.get(p))
                    .map_or(TextStyle::INITIAL, text_style);
                let item = ifc.atomics.len();
                ifc.atomics.push(b);
                push_unit(
                    &mut ifc,
                    Unit {
                        ch: '\u{FFFC}',
                        kind: Kind::Atomic,
                        item,
                        offset: 0,
                        style,
                    },
                    0,
                );
            }
            // A marker is placed beside its list item, not in its lines.
            _ => {}
        }
    }
    ifc.wraps = opportunities(&ifc.units);
    for (run, mine) in runs {
        if let Some(style) = styles.get(run) {
            shape_run(&mut ifc, &mine, style, fonts);
        }
    }
    ifc
}

/// The used horizontal margins, borders and padding of an inline box with
/// style `s` in a containing block of width `cb` (§10.3.1: "A computed value
/// of 'auto' for 'margin-left' or 'margin-right' becomes a used value of
/// '0'"): (start edge, end edge) widths, and each part.
pub fn inline_edges(s: &ComputedStyle, cb: i32) -> InlineEdges {
    let [mt, mr, mb, ml] = s.margin;
    let [pt, pr, pb, pl] = s.padding;
    let [bt, br, bb, bl] = s.border_width;
    let m = |v| size(v, cb).unwrap_or(0);
    InlineEdges {
        margin: super::fragment::Sides {
            top: m(mt),
            right: m(mr),
            bottom: m(mb),
            left: m(ml),
        },
        border: super::fragment::Sides {
            top: bt,
            right: br,
            bottom: bb,
            left: bl,
        },
        padding: super::fragment::Sides {
            top: lp(pt, cb),
            right: lp(pr, cb),
            bottom: lp(pb, cb),
            left: lp(pl, cb),
        },
    }
}

/// An inline box's used margins, borders and padding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct InlineEdges {
    /// Margins.
    pub margin: super::fragment::Sides,
    /// Borders.
    pub border: super::fragment::Sides,
    /// Padding.
    pub padding: super::fragment::Sides,
}

impl InlineEdges {
    /// The start edge's width.
    pub fn start(&self) -> i32 {
        self.margin
            .left
            .saturating_add(self.border.left)
            .saturating_add(self.padding.left)
    }

    /// The end edge's width.
    pub fn end(&self) -> i32 {
        self.padding
            .right
            .saturating_add(self.border.right)
            .saturating_add(self.margin.right)
    }

    /// Its left and right borders and padding are zero (§3.3's first
    /// condition, in a horizontal writing mode).
    pub fn no_horizontal_edges(&self) -> bool {
        self.border.left == 0
            && self.border.right == 0
            && self.padding.left == 0
            && self.padding.right == 0
    }
}

/// Each unit's leading and trailing edge widths: the start edges of the
/// inline boxes whose first unit it is, and the end edges of those whose
/// last unit it is (the module's modelling choices), with `edges[i]` the
/// edges of `ifc.inlines[i]`.
pub fn unit_edges(ifc: &Ifc, edges: &[InlineEdges]) -> (Vec<i32>, Vec<i32>) {
    let n = ifc.units.len();
    let mut lead = vec![0i32; n];
    let mut trail = vec![0i32; n];
    for (info, e) in ifc.inlines.iter().zip(edges) {
        if info.units.is_empty() {
            continue;
        }
        if info.first
            && let Some(l) = lead.get_mut(info.units.start)
        {
            *l = l.saturating_add(e.start());
        }
        if info.last
            && let Some(t) = trail.get_mut(info.units.end.saturating_sub(1))
        {
            *t = t.saturating_add(e.end());
        }
    }
    (lead, trail)
}

/// CSS 2.1 §16.2 with CSS Text 3 §7.1†'s overflow rule, the step `state.rs`
/// states: the offset of a line's content of width `width` in a line box of
/// width `available`.
pub fn align_offset(align: Align, available: i32, width: i32) -> i32 {
    let slack = available.saturating_sub(width);
    if slack <= 0 {
        return 0;
    }
    match align {
        Align::Left => 0,
        Align::Right => slack,
        Align::Center => half_down(slack),
    }
}

impl LineExtent {
    /// The extent with a box from `top` to `bottom` added (a box given
    /// upside down counts as the point at its top).
    pub fn add(self, top: i32, bottom: i32) -> LineExtent {
        let bottom = bottom.max(top);
        if self.any {
            LineExtent {
                top: self.top.min(top),
                bottom: self.bottom.max(bottom),
                any: true,
            }
        } else {
            LineExtent {
                top,
                bottom,
                any: true,
            }
        }
    }
}

/// What line layout needs of an atomic inline, laid out already.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AtomicSize {
    /// Its margin box's width.
    pub width: i32,
    /// Its margin box's height.
    pub height: i32,
    /// Its baseline, down from its margin box's top, if it has one.
    pub baseline: Option<i32>,
    /// Its used left margin and top margin (from its margin box to its
    /// border box).
    pub margin_left: i32,
    /// Its used top margin.
    pub margin_top: i32,
}

/// What line layout gives back.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Lines {
    /// The line boxes, in the container's content box coordinates.
    pub lines: Vec<LineBox>,
    /// The bottom of the last line box (the content height they take).
    pub height: i32,
    /// Some line box is not empty.
    pub content: bool,
    /// The first and last non-empty line boxes' baselines.
    pub first_baseline: Option<i32>,
    /// The last.
    pub last_baseline: Option<i32>,
    /// Each atomic inline's border box position.
    pub atomics: Vec<(BoxId, i32, i32)>,
    /// Each inline box's bounding border box over its pieces.
    pub inlines: Vec<(BoxId, Rect)>,
}

/// Everything line layout reads of the context's surroundings.
pub struct LineContext<'a, F: TextFns> {
    /// The box tree.
    pub tree: &'a BoxTree,
    /// Every box's computed style.
    pub styles: &'a [ComputedStyle],
    /// The fonts.
    pub fonts: &'a F,
    /// Quirks or limited-quirks mode (§3.3, §3.4).
    pub quirks: bool,
    /// The container's content width.
    pub width: i32,
    /// Its first line may be indented (§16.1's first-line condition).
    pub indent_first: bool,
    /// Each atomic inline's size.
    pub atomic: &'a dyn Fn(BoxId) -> AtomicSize,
}

/// One box on a line, for vertical alignment.
#[derive(Debug, Clone, Copy)]
struct OnLine {
    /// Its frame: 0 for the root inline box's, else its own index plus one
    /// for a `top` or `bottom` aligned box, or its parent's.
    frame: usize,
    /// Its baseline, relative to its frame's root's baseline.
    baseline: i32,
    /// Its extent above and below its baseline.
    above: i32,
    /// Below.
    below: i32,
    /// It counts for the line's height.
    counts: bool,
    /// `top` (`Some(true)`) or `bottom` (`Some(false)`) aligned.
    edge: Option<bool>,
}

/// The font facts vertical alignment reads of a box.
#[derive(Debug, Clone, Copy)]
struct FontFacts {
    metrics: FontMetrics,
    line_height: i32,
    size: i32,
}

fn font_facts(style: &ComputedStyle, fonts: &impl TextFns) -> FontFacts {
    let metrics = fonts.metrics(style);
    FontFacts {
        metrics,
        line_height: line_height(style, &metrics),
        size: style.font_size,
    }
}

/// §10.8.1: the baseline of a box aligned by `va` in a parent whose
/// baseline is `parent` and whose font facts are `p`, given the box's own
/// extent above and below its baseline and line height (`None` for `top`
/// and `bottom`, which align to the line box).
fn shift(va: VerticalAlign, parent: i32, p: &FontFacts, above: i32, below: i32, lh: i32) -> i32 {
    match va {
        // "Align the baseline of the box with the baseline of the parent
        // box."
        VerticalAlign::Baseline | VerticalAlign::Top | VerticalAlign::Bottom => parent,
        // "Align the vertical midpoint of the box with the baseline of the
        // parent box plus half the x-height of the parent."
        VerticalAlign::Middle => {
            let mid = parent.saturating_sub(half_down(p.metrics.x_height));
            mid.saturating_sub(half_down(below.saturating_sub(above)))
        }
        // "Lower the baseline of the box to the proper position for
        // subscripts of the parent's box" (a fifth of its font size).
        VerticalAlign::Sub => parent.saturating_add(p.size.div_euclid(5)),
        // "Raise the baseline of the box to the proper position for
        // superscripts of the parent's box" (a third of its font size).
        VerticalAlign::Super => parent.saturating_sub(p.size.div_euclid(3)),
        // "Align the top of the box with the top of the parent's content
        // area."
        VerticalAlign::TextTop => parent
            .saturating_sub(p.metrics.ascent)
            .saturating_add(above),
        // "Align the bottom of the box with the bottom of the parent's
        // content area."
        VerticalAlign::TextBottom => parent
            .saturating_add(p.metrics.descent)
            .saturating_sub(below),
        // "<percentage>: Raise … the box by this distance (a percentage of
        // the 'line-height' value)"; "<length>: Raise … the box by this
        // distance."
        VerticalAlign::Lp(v) => parent.saturating_sub(lp(v, lh)),
    }
}

/// Lays out the lines of `ifc` (see the module's modelling choices).
pub fn layout_lines<F: TextFns>(ifc: &Ifc, cx: &LineContext<'_, F>) -> Lines {
    let n = ifc.units.len();
    let cstyle = cx.styles.get(ifc.container);
    let initial = ComputedStyle::initial();
    let cstyle = cstyle.unwrap_or(&initial);
    let w = cx.width;
    // Each inline box's used edges and font facts, and the root's.
    let edges: Vec<InlineEdges> = ifc
        .inlines
        .iter()
        .map(|i| {
            cx.styles
                .get(i.id)
                .map_or(InlineEdges::default(), |s| inline_edges(s, w))
        })
        .collect();
    let facts: Vec<FontFacts> = ifc
        .inlines
        .iter()
        .map(|i| font_facts(cx.styles.get(i.id).unwrap_or(&initial), cx.fonts))
        .collect();
    let root = font_facts(cstyle, cx.fonts);
    let (lead, trail) = unit_edges(ifc, &edges);
    let atomic_width = |k: usize| -> i32 { ifc.owner.get(k).map_or(0, |&b| (cx.atomic)(b).width) };
    let base_advance = |k: usize, pen: i32| -> i32 {
        let Some(u) = ifc.units.get(k) else { return 0 };
        match u.kind {
            Kind::Atomic => atomic_width(k),
            Kind::PreservedTab => {
                let (size, half) = ifc.tab.get(k).copied().unwrap_or((0, 0));
                tab_advance(pen, size, half)
            }
            _ => ifc.advance.get(k).copied().unwrap_or(0),
        }
    };
    // §16.1 and CSS Text 3's `each-line` and `hanging`.
    let ti = &cstyle.text_indent;
    let indent_len = lp(ti.length, w);
    let indented = |line: usize, after_forced: bool| -> bool {
        let base = (line == 0 && cx.indent_first) || (ti.each_line && after_forced);
        base != ti.hanging
    };

    // Choosing lines: item 5.12's first fit, with each line's width.
    let mut chosen: Vec<(usize, usize, bool, i32)> = Vec::new();
    let mut state = FitState::new(0);
    let mut i = 0usize;
    let mut indent = if indented(0, false) { indent_len } else { 0 };
    for _ in 0..n.saturating_mul(2).saturating_add(2) {
        if state.start >= n {
            break;
        }
        let available = w.saturating_sub(indent);
        let Some(u) = ifc.units.get(i) else {
            chosen.push((state.start, n, true, indent));
            break;
        };
        let advance = if state.m.takes_width(u) {
            base_advance(i, state.m.pen.saturating_add(indent))
                .saturating_add(lead.get(i).copied().unwrap_or(0))
                .saturating_add(trail.get(i).copied().unwrap_or(0))
        } else {
            0
        };
        let wrap = ifc.wraps.get(i).copied().unwrap_or(Wrap::Forced);
        match fit_step(&state, i, u, advance, wrap, available) {
            Fit::Continue(next) => {
                state = next;
                i = i.saturating_add(1);
            }
            Fit::End { end, forced, .. } => {
                chosen.push((state.start, end, forced, indent));
                indent = if indented(chosen.len(), forced) {
                    indent_len
                } else {
                    0
                };
                state = FitState::new(end);
                i = end;
            }
        }
    }

    let align = line_align(cstyle.text_align);
    let mut out = Lines::default();
    let mut y = 0i32;
    let mut bounds: Vec<Option<Rect>> = vec![None; ifc.inlines.len()];
    let mut stamp: Vec<usize> = vec![usize::MAX; ifc.inlines.len()];
    for (line_no, &(start, end, forced, indent)) in chosen.iter().enumerate() {
        let t = trim(&ifc.units, start, end, forced);
        let fb = end.checked_sub(1).filter(|&k| {
            forced
                && ifc
                    .units
                    .get(k)
                    .is_some_and(|u| u.kind == Kind::ForcedBreak)
        });
        let kept = |k: usize| (t.start..t.end).contains(&k) || Some(k) == fb;
        // Horizontal: the pen through the kept units and their edges.
        let mut x = vec![0i32; end.saturating_sub(start)];
        let mut pen = indent;
        let mut hang_pen = None;
        let mut content_start: HashMap<usize, i32> = HashMap::new();
        let mut content_end: HashMap<usize, i32> = HashMap::new();
        let mut edge_on_line = false;
        let mut empty = true;
        let mut last_pen = pen;
        for k in start..end {
            if k == t.hang {
                hang_pen = Some(pen);
            }
            if !kept(k) {
                continue;
            }
            // The inline boxes first met on this line at this unit (each
            // one's ancestors were met before it, or now), outermost first;
            // a box's start edge is drawn where its first unit is.
            let mut chain = Vec::new();
            let mut p = ifc.parent.get(k).copied().flatten();
            while let Some(j) = p {
                if content_start.contains_key(&j) {
                    break;
                }
                chain.push(j);
                p = ifc.inlines.get(j).and_then(|info| info.parent);
            }
            for &j in chain.iter().rev() {
                let Some(info) = ifc.inlines.get(j) else {
                    continue;
                };
                if info.units.start == k && info.first {
                    let e = edges.get(j).copied().unwrap_or_default();
                    pen = pen.saturating_add(e.start());
                    edge_on_line |= e.start() != 0;
                }
                content_start.insert(j, pen);
            }
            if let Some(slot) = x.get_mut(k.saturating_sub(start)) {
                *slot = pen;
            }
            pen = pen.saturating_add(base_advance(k, pen));
            if let Some(u) = ifc.units.get(k)
                && (matches!(
                    u.kind,
                    Kind::Char
                        | Kind::PreservedSpace
                        | Kind::PreservedTab
                        | Kind::OtherSpace
                        | Kind::Atomic
                ) || Some(k) == fb)
            {
                empty = false;
            }
            // The inline boxes whose last unit this is, innermost first (if
            // a box does not end here, neither does any ancestor).
            let mut p = ifc.parent.get(k).copied().flatten();
            while let Some(j) = p {
                let Some(info) = ifc.inlines.get(j) else {
                    break;
                };
                if info.units.end != k.saturating_add(1) {
                    break;
                }
                content_end.insert(j, pen);
                if info.last {
                    let e = edges.get(j).copied().unwrap_or_default();
                    pen = pen.saturating_add(e.end());
                    edge_on_line |= e.end() != 0;
                }
                p = info.parent;
            }
            last_pen = pen;
        }
        empty &= !edge_on_line;
        let content_width = hang_pen.unwrap_or(pen).saturating_sub(indent);
        let line_available = w.saturating_sub(indent);
        let offset = align_offset(align, line_available, content_width);
        for v in &mut x {
            *v = v.saturating_add(offset);
        }

        // Vertical (§10.8): the boxes on the line, parents first.
        let mut present: Vec<usize> = Vec::new();
        let mut text_in: HashMap<usize, bool> = HashMap::new();
        let mut root_text = false;
        for k in start..end {
            if !kept(k) {
                continue;
            }
            let is_text = ifc.units.get(k).is_some_and(|u| {
                matches!(
                    u.kind,
                    Kind::Char
                        | Kind::PreservedSpace
                        | Kind::PreservedTab
                        | Kind::OtherSpace
                        | Kind::ForcedBreak
                )
            });
            let mut p = ifc.parent.get(k).copied().flatten();
            if p.is_none() && is_text {
                root_text = true;
            }
            while let Some(j) = p {
                let seen = stamp.get(j) == Some(&line_no);
                if seen && (!is_text || text_in.get(&j).copied().unwrap_or(false)) {
                    // This box and its ancestors are marked already.
                    break;
                }
                if is_text {
                    text_in.insert(j, true);
                }
                if stamp.get(j) != Some(&line_no) {
                    if let Some(s) = stamp.get_mut(j) {
                        *s = line_no;
                    }
                    present.push(j);
                }
                p = ifc.inlines.get(j).and_then(|info| info.parent);
            }
        }
        present.sort_unstable();
        // Positions in `present` by inline index.
        let mut slot: HashMap<usize, usize> = HashMap::new();
        let mut boxes: Vec<OnLine> = Vec::with_capacity(present.len());
        for &j in &present {
            let info = ifc.inlines.get(j);
            let style = info.and_then(|i| cx.styles.get(i.id)).unwrap_or(&initial);
            let f = facts.get(j).copied().unwrap_or(root);
            let parent = info
                .and_then(|i| i.parent)
                .and_then(|pj| slot.get(&pj).copied());
            let (pf, pb, pframe) = match parent {
                Some(ps) => (
                    present
                        .get(ps)
                        .and_then(|&pj| facts.get(pj).copied())
                        .unwrap_or(root),
                    boxes.get(ps).map_or(0, |b| b.baseline),
                    boxes.get(ps).map_or(0, |b| b.frame),
                ),
                None => (root, 0, 0),
            };
            let zero = cx.quirks
                && edges.get(j).is_some_and(InlineEdges::no_horizontal_edges)
                && !text_in.get(&j).copied().unwrap_or(false);
            let (above, below) = half_leading(f.metrics.ascent, f.metrics.descent, f.line_height);
            let edge = match style.vertical_align {
                VerticalAlign::Top => Some(true),
                VerticalAlign::Bottom => Some(false),
                _ => None,
            };
            let (baseline, frame) = if edge.is_some() {
                (0, boxes.len().saturating_add(1))
            } else {
                (
                    shift(style.vertical_align, pb, &pf, above, below, f.line_height),
                    pframe,
                )
            };
            slot.insert(j, boxes.len());
            boxes.push(OnLine {
                frame,
                baseline,
                above,
                below,
                counts: !zero,
                edge,
            });
        }
        // Atomic inlines on the line.
        let mut atomics: HashMap<usize, usize> = HashMap::new();
        for k in start..end {
            if !kept(k) || ifc.units.get(k).is_none_or(|u| u.kind != Kind::Atomic) {
                continue;
            }
            let Some(&b) = ifc.owner.get(k) else { continue };
            let a = (cx.atomic)(b);
            let style = cx.styles.get(b).unwrap_or(&initial);
            let parent = ifc
                .parent
                .get(k)
                .copied()
                .flatten()
                .and_then(|pj| slot.get(&pj).copied());
            let (pf, pb, pframe) = match parent {
                Some(ps) => (
                    present
                        .get(ps)
                        .and_then(|&pj| facts.get(pj).copied())
                        .unwrap_or(root),
                    boxes.get(ps).map_or(0, |b| b.baseline),
                    boxes.get(ps).map_or(0, |b| b.frame),
                ),
                None => (root, 0, 0),
            };
            let above = a.baseline.unwrap_or(a.height);
            let below = a.height.saturating_sub(above);
            let edge = match style.vertical_align {
                VerticalAlign::Top => Some(true),
                VerticalAlign::Bottom => Some(false),
                _ => None,
            };
            let (baseline, frame) = if edge.is_some() {
                (0, boxes.len().saturating_add(1))
            } else {
                (
                    shift(style.vertical_align, pb, &pf, above, below, a.height),
                    pframe,
                )
            };
            atomics.insert(k, boxes.len());
            boxes.push(OnLine {
                frame,
                baseline,
                above,
                below,
                counts: true,
                edge,
            });
        }
        // Extents: the root's frame, then each `top` or `bottom` frame.
        let root_counts = !empty && (!cx.quirks || root_text);
        let (r_above, r_below) =
            half_leading(root.metrics.ascent, root.metrics.descent, root.line_height);
        let mut frames: Vec<LineExtent> = vec![LineExtent::EMPTY; boxes.len().saturating_add(1)];
        if root_counts && let Some(f) = frames.get_mut(0) {
            *f = f.add(r_above.saturating_neg(), r_below);
        }
        for b in &boxes {
            if b.counts
                && let Some(f) = frames.get_mut(b.frame)
            {
                *f = f.add(
                    b.baseline.saturating_sub(b.above),
                    b.baseline.saturating_add(b.below),
                );
            }
        }
        let main = frames.first().copied().unwrap_or(LineExtent::EMPTY);
        let (mut top, mut bottom) = (main.top, main.bottom);
        let mut frame_base: Vec<i32> = vec![0; frames.len()];
        for pass in [true, false] {
            for (bi, b) in boxes.iter().enumerate() {
                if b.edge != Some(pass) {
                    continue;
                }
                let fe = frames
                    .get(bi.saturating_add(1))
                    .copied()
                    .unwrap_or(LineExtent::EMPTY);
                let h = fe.bottom.saturating_sub(fe.top);
                if pass {
                    bottom = bottom.max(top.saturating_add(h));
                } else {
                    top = top.min(bottom.saturating_sub(h));
                }
            }
        }
        for (bi, b) in boxes.iter().enumerate() {
            if let Some(edge) = b.edge {
                let fe = frames
                    .get(bi.saturating_add(1))
                    .copied()
                    .unwrap_or(LineExtent::EMPTY);
                if let Some(fb) = frame_base.get_mut(bi.saturating_add(1)) {
                    *fb = if edge {
                        top.saturating_sub(fe.top)
                    } else {
                        bottom.saturating_sub(fe.bottom)
                    };
                }
            }
        }
        let height = if empty {
            0
        } else {
            bottom.saturating_sub(top).max(0)
        };
        let baseline = if empty { y } else { y.saturating_sub(top) };
        let abs_base = |b: &OnLine| {
            baseline
                .saturating_add(frame_base.get(b.frame).copied().unwrap_or(0))
                .saturating_add(b.baseline)
        };

        // Items: inline pieces, glyph runs, atomics.
        let mut items: Vec<LineItem> = Vec::new();
        for (pos, &j) in present.iter().enumerate() {
            let (Some(info), Some(b)) = (ifc.inlines.get(j), boxes.get(pos)) else {
                continue;
            };
            let f = facts.get(j).copied().unwrap_or(root);
            let e = edges.get(j).copied().unwrap_or_default();
            let cs = content_start
                .get(&j)
                .copied()
                .unwrap_or(0)
                .saturating_add(offset);
            // A box that goes on to the next line, or whose last unit Phase
            // II removed, ends with the line's content.
            let ce = content_end
                .get(&j)
                .copied()
                .unwrap_or(last_pen)
                .saturating_add(offset);
            let start_edge =
                info.first && (start..end).contains(&info.units.start) && kept(info.units.start);
            let end_edge = info.last
                && info
                    .units
                    .end
                    .checked_sub(1)
                    .is_some_and(|l| (start..end).contains(&l) && kept(l));
            let left = if start_edge {
                cs.saturating_sub(e.padding.left)
            } else {
                cs
            };
            let right = if end_edge {
                ce.saturating_add(e.padding.right)
            } else {
                ce
            };
            let bl = abs_base(b);
            let rect = Rect {
                x: left,
                y: bl.saturating_sub(f.metrics.ascent),
                width: right.saturating_sub(left).max(0),
                height: f.metrics.ascent.saturating_add(f.metrics.descent).max(0),
            };
            let border_rect = Rect {
                x: rect
                    .x
                    .saturating_sub(if start_edge { e.border.left } else { 0 }),
                y: rect
                    .y
                    .saturating_sub(e.padding.top)
                    .saturating_sub(e.border.top),
                width: rect
                    .width
                    .saturating_add(if start_edge { e.border.left } else { 0 })
                    .saturating_add(if end_edge { e.border.right } else { 0 }),
                height: rect
                    .height
                    .saturating_add(e.padding.vertical())
                    .saturating_add(e.border.vertical()),
            };
            if let Some(slot) = bounds.get_mut(j) {
                *slot = Some(match *slot {
                    None => border_rect,
                    Some(r) => union(r, border_rect),
                });
            }
            items.push(LineItem::Inline(InlinePiece {
                inline: info.id,
                rect,
                start_edge,
                end_edge,
            }));
        }
        let mut run: Option<GlyphRun> = None;
        for k in t.start..t.end {
            let (Some(u), Some(&owner)) = (ifc.units.get(k), ifc.owner.get(k)) else {
                continue;
            };
            let ux = x.get(k.saturating_sub(start)).copied().unwrap_or(0);
            if u.kind == Kind::Atomic {
                if let Some(r) = run.take() {
                    items.push(LineItem::Text(r));
                }
                let a = (cx.atomic)(owner);
                let b = atomics.get(&k).and_then(|&bi| boxes.get(bi));
                let margin_top_edge = b.map_or(baseline, |b| abs_base(b).saturating_sub(b.above));
                out.atomics.push((
                    owner,
                    ux.saturating_add(a.margin_left),
                    margin_top_edge.saturating_add(a.margin_top),
                ));
                items.push(LineItem::Atomic(owner));
                continue;
            }
            let base = ifc
                .parent
                .get(k)
                .copied()
                .flatten()
                .and_then(|j| slot.get(&j))
                .and_then(|&s| boxes.get(s))
                .map_or(baseline, abs_base);
            let size = cx.styles.get(owner).map_or(0, |s| s.font_size);
            let range = ifc.glyph_range.get(k).cloned().unwrap_or(0..0);
            let mut gx = ux;
            for g in ifc.glyphs.get(range).unwrap_or(&[]) {
                let same = run
                    .as_ref()
                    .is_some_and(|r| r.source == owner && r.face == g.face && r.baseline == base);
                if !same {
                    if let Some(r) = run.take() {
                        items.push(LineItem::Text(r));
                    }
                    run = Some(GlyphRun {
                        source: owner,
                        face: g.face,
                        size,
                        x: gx,
                        baseline: base,
                        glyphs: Vec::new(),
                    });
                }
                if let Some(r) = run.as_mut() {
                    r.glyphs.push(Glyph {
                        id: g.id,
                        x: gx.saturating_sub(r.x).saturating_add(g.x_offset),
                        y: g.y_offset,
                        advance: g.advance,
                        unit: ifc.in_run.get(k).copied().unwrap_or(0),
                    });
                }
                gx = gx.saturating_add(g.advance);
            }
        }
        if let Some(r) = run.take() {
            items.push(LineItem::Text(r));
        }
        out.lines.push(LineBox {
            container: ifc.container,
            rect: Rect {
                x: 0,
                y,
                width: w.max(0),
                height,
            },
            baseline,
            items,
        });
        if !empty {
            out.content = true;
            if out.first_baseline.is_none() {
                out.first_baseline = Some(baseline);
            }
            out.last_baseline = Some(baseline);
        }
        y = y.saturating_add(height);
    }
    out.height = y;
    out.inlines = ifc
        .inlines
        .iter()
        .zip(bounds)
        .filter_map(|(info, r)| r.map(|r| (info.id, r)))
        .collect();
    out
}

/// The smallest rectangle holding `a` and `b`.
pub fn union(a: Rect, b: Rect) -> Rect {
    let x = a.x.min(b.x);
    let y = a.y.min(b.y);
    let right = a.right().max(b.right());
    let bottom = a.bottom().max(b.bottom());
    Rect {
        x,
        y,
        width: right.saturating_sub(x),
        height: bottom.saturating_sub(y),
    }
}

/// The min-content and max-content widths of `ifc` (CSS Text 3 §5, item
/// 5.12's `min_content` and `max_content`), with each atomic inline's
/// contribution `atomic(b) = (min, max)`, inline boxes' edges with
/// percentages as zero, and a positive text indent added to the
/// max-content width.
pub fn intrinsic(
    ifc: &Ifc,
    styles: &[ComputedStyle],
    atomic: &dyn Fn(BoxId) -> (i32, i32),
    keep_images: Option<&dyn Fn(BoxId) -> bool>,
) -> (i32, i32) {
    let edges: Vec<InlineEdges> = ifc
        .inlines
        .iter()
        .map(|i| {
            styles
                .get(i.id)
                .map_or(InlineEdges::default(), |s| inline_edges(s, 0))
        })
        .collect();
    let (lead, trail) = unit_edges(ifc, &edges);
    let width = |k: usize, pen: i32, max: bool| -> i32 {
        let Some(u) = ifc.units.get(k) else { return 0 };
        let base = match u.kind {
            Kind::Atomic => ifc.owner.get(k).map_or(0, |&b| {
                let (lo, hi) = atomic(b);
                if max { hi } else { lo }
            }),
            Kind::PreservedTab => {
                let (size, half) = ifc.tab.get(k).copied().unwrap_or((0, 0));
                tab_advance(pen, size, half)
            }
            _ => ifc.advance.get(k).copied().unwrap_or(0),
        };
        base.saturating_add(lead.get(k).copied().unwrap_or(0))
            .saturating_add(trail.get(k).copied().unwrap_or(0))
    };
    // The Quirks Mode Standard's §3.8 (item 5.15): in the min-content width
    // of an auto-width table cell's own inline formatting context, "img
    // elements that are inline-level replaced elements … must not have a
    // soft wrap opportunity before or after them".
    let quirk_wraps: Option<Vec<Wrap>> = keep_images.map(|is_image| {
        let mut wraps = ifc.wraps.clone();
        for (k, u) in ifc.units.iter().enumerate() {
            let image =
                matches!(u.kind, Kind::Atomic) && ifc.owner.get(k).is_some_and(|&b| is_image(b));
            if !image {
                continue;
            }
            for at in [k.checked_sub(1), Some(k)].into_iter().flatten() {
                if let Some(w) = wraps.get_mut(at)
                    && matches!(w, Wrap::Soft | Wrap::Emergency { .. })
                {
                    *w = Wrap::None;
                }
            }
        }
        wraps
    });
    let wraps = quirk_wraps.as_deref().unwrap_or(&ifc.wraps);
    let min = crate::text::lines::min_content(&ifc.units, wraps, |k, pen| width(k, pen, false));
    let max = crate::text::lines::max_content(&ifc.units, &ifc.wraps, |k, pen| width(k, pen, true));
    let indent = styles
        .get(ifc.container)
        .map_or(0, |s| lp(s.text_indent.length, 0))
        .max(0);
    (min, max.saturating_add(indent).max(min))
}
