//! The output of block and inline formatting: a fragment tree keyed by box
//! id (phase-5.md item 5.14: "the result is a fragment tree (boxes with
//! positions and sizes, line boxes with positioned glyph runs) keyed by box
//! id, mapping back to node ids for hit testing").
//!
//! Modelling choices:
//!
//! - **Lengths are 1/64 px in `i32`** (26.6 fixed point, the unit of
//!   `clazel-style`'s computed lengths and of item 5.11's glyph positions).
//!   Every sum saturates (`flow/length.rs`), so a hostile page can push a
//!   coordinate to `i32::MAX` but never overflow.
//! - **Coordinates are the document's**: the origin is the top left corner
//!   of the initial containing block (CSS 2.1 §10.1), y grows downwards.
//!   Scrolling is the renderer's (item 5.20) and does not change them.
//! - **One [`BoxFragment`] per box that is laid out as a box**: the root
//!   (the initial containing block), block-level boxes, atomic inlines
//!   (inline blocks, replaced elements, inline table wrappers), markers, the
//!   table placeholder's boxes (`flow/mod.rs`), and inline boxes, whose
//!   fragment is the bounding rectangle of their pieces with their used
//!   margins, borders and padding. Text runs have none: their glyphs are in
//!   the line boxes. A box that is not laid out has `None`.
//! - **An inline box has one [`InlinePiece`] per line box it is on** (CSS
//!   2.1 §9.4.2: "it is split into several boxes and these boxes are
//!   distributed across several line boxes"), each saying whether the box's
//!   start and end edges are on that line, so item 5.16 draws borders where
//!   §9.4.2 says ("margins, borders, and padding have no visual effect where
//!   the split occurs").
//! - **A list item's marker** gets a line box of its own, holding its text,
//!   whose container is the marker box (`flow/mod.rs`, markers).

use std::ops::Range;

use crate::boxes::BoxId;

/// A rectangle in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Rect {
    /// Left edge.
    pub x: i32,
    /// Top edge.
    pub y: i32,
    /// Width (never negative in a fragment the layout makes).
    pub width: i32,
    /// Height (never negative in a fragment the layout makes).
    pub height: i32,
}

/// Four lengths, one per side, in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Sides {
    /// Top.
    pub top: i32,
    /// Right.
    pub right: i32,
    /// Bottom.
    pub bottom: i32,
    /// Left.
    pub left: i32,
}

impl Sides {
    /// All four zero.
    pub const ZERO: Sides = Sides {
        top: 0,
        right: 0,
        bottom: 0,
        left: 0,
    };

    /// Left plus right, saturating.
    pub fn horizontal(&self) -> i32 {
        self.left.saturating_add(self.right)
    }

    /// Top plus bottom, saturating.
    pub fn vertical(&self) -> i32 {
        self.top.saturating_add(self.bottom)
    }
}

impl Rect {
    /// `self` grown by `s` on each side (saturating).
    pub fn outset(&self, s: &Sides) -> Rect {
        Rect {
            x: self.x.saturating_sub(s.left),
            y: self.y.saturating_sub(s.top),
            width: self.width.saturating_add(s.horizontal()),
            height: self.height.saturating_add(s.vertical()),
        }
    }

    /// `self` shrunk by `s` on each side (saturating; a size never goes
    /// below zero).
    pub fn inset(&self, s: &Sides) -> Rect {
        Rect {
            x: self.x.saturating_add(s.left),
            y: self.y.saturating_add(s.top),
            width: self.width.saturating_sub(s.horizontal()).max(0),
            height: self.height.saturating_sub(s.vertical()).max(0),
        }
    }

    /// The bottom edge, saturating.
    pub fn bottom(&self) -> i32 {
        self.y.saturating_add(self.height)
    }

    /// The right edge, saturating.
    pub fn right(&self) -> i32 {
        self.x.saturating_add(self.width)
    }
}

/// The geometry of one box (CSS 2.1 §8.1, the box model), in document
/// coordinates, with the used values of its margins, borders and padding.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BoxFragment {
    /// The border box.
    pub border_box: Rect,
    /// Used margins (may be negative).
    pub margin: Sides,
    /// Used border widths.
    pub border: Sides,
    /// Used padding.
    pub padding: Sides,
    /// The baseline of its first line box in flow, if it has one (y, in
    /// document coordinates); a list item's marker is aligned with it.
    pub first_baseline: Option<i32>,
    /// The baseline of its last line box in flow, if it has one; an inline
    /// block's baseline (CSS 2.1 §10.8.1, `vertical-align: baseline`).
    pub last_baseline: Option<i32>,
    /// Its own line boxes, as indexes into [`FragmentTree::lines`] (empty
    /// unless it is a block container with inline content, or a marker).
    pub lines: Range<usize>,
}

impl BoxFragment {
    /// The padding box.
    pub fn padding_box(&self) -> Rect {
        self.border_box.inset(&self.border)
    }

    /// The content box.
    pub fn content_box(&self) -> Rect {
        self.padding_box().inset(&self.padding)
    }

    /// The margin box (CSS 2.1 §8.1: "the margin edge surrounds the box
    /// margin"; negative margins shrink it).
    pub fn margin_box(&self) -> Rect {
        self.border_box.outset(&self.margin)
    }
}

/// One glyph of a run, placed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Glyph {
    /// The glyph id in the run's face.
    pub id: u16,
    /// Its origin, from the run's origin (1/64 px).
    pub x: i32,
    /// Its vertical offset, down from the baseline (1/64 px).
    pub y: i32,
    /// Its advance (1/64 px).
    pub advance: i32,
    /// The index of the unit it draws among its text run's units (item
    /// 5.12's [`crate::text::Unit`]s), for hit testing and selection.
    pub unit: usize,
}

/// Glyphs of one text run in one face, on one line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlyphRun {
    /// The text run box (or marker box) the glyphs belong to; its style
    /// gives their colour and decorations (item 5.16).
    pub source: BoxId,
    /// The face, as [`super::fonts::TextFns`] numbers faces.
    pub face: u32,
    /// The used font size (1/64 px per em).
    pub size: i32,
    /// The pen position of the first glyph (x, document coordinates).
    pub x: i32,
    /// The baseline (y, document coordinates).
    pub baseline: i32,
    /// The glyphs, in logical order.
    pub glyphs: Vec<Glyph>,
}

/// The part of an inline box on one line box.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InlinePiece {
    /// The inline box (or fragment of a split one, item 5.13).
    pub inline: BoxId,
    /// Its content area on this line (CSS 2.1 §10.6.1: from the top of the
    /// first available font's ascent to the bottom of its descent) widened
    /// by the horizontal padding of the edges on this line: the rectangle
    /// its background fills.
    pub rect: Rect,
    /// Its start (left) edge is on this line.
    pub start_edge: bool,
    /// Its end (right) edge is on this line.
    pub end_edge: bool,
}

/// What a line box holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LineItem {
    /// Glyphs of a text run.
    Text(GlyphRun),
    /// A piece of an inline box.
    Inline(InlinePiece),
    /// An atomic inline, whose [`BoxFragment`] holds its geometry.
    Atomic(BoxId),
}

/// A line box (CSS 2.1 §9.4.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineBox {
    /// The block container (or marker box) whose line box it is.
    pub container: BoxId,
    /// Its rectangle: the containing block's content width (less the text
    /// indent on a first line, CSS 2.1 §16.1) and its height (§10.8).
    pub rect: Rect,
    /// Its baseline: the root inline box's (the strut's), y in document
    /// coordinates.
    pub baseline: i32,
    /// What it holds, in content order: each inline box's piece before the
    /// content inside it.
    pub items: Vec<LineItem>,
}

/// The fragment tree of a box tree.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FragmentTree {
    /// `boxes[b]` is box `b`'s fragment, if it is laid out as a box.
    pub boxes: Vec<Option<BoxFragment>>,
    /// Every line box, grouped by container in tree order.
    pub lines: Vec<LineBox>,
    /// `nodes[b]` is the DOM node that generated box `b` (`None` for an
    /// anonymous box): the map back to node ids for hit testing.
    pub nodes: Vec<Option<usize>>,
    /// The initial containing block: the viewport's size at the origin.
    pub viewport: Rect,
    /// The document's extent: the union of the viewport and every border
    /// box and line box (a scrolling bound for item 5.20; `overflow` is not
    /// applied to it).
    pub extent: Rect,
}

impl FragmentTree {
    /// Box `b`'s fragment.
    pub fn fragment(&self, b: BoxId) -> Option<&BoxFragment> {
        self.boxes.get(b).and_then(Option::as_ref)
    }

    /// The node that generated box `b`.
    pub fn node(&self, b: BoxId) -> Option<usize> {
        self.nodes.get(b).copied().flatten()
    }

    /// Box `b`'s own line boxes.
    pub fn lines_of(&self, b: BoxId) -> &[LineBox] {
        self.fragment(b)
            .and_then(|f| self.lines.get(f.lines.clone()))
            .unwrap_or(&[])
    }
}
