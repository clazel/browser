//! The display list's types, the states of the paint walk, their
//! invariants, and the contracts of the steps over them (phase-5.md item
//! 5.16).
//!
//! As in `flow/state.rs` and `table/state.rs`: each loop of painting is a
//! fold of a step over a small state whose invariant is written here as a
//! function; a Kani harness over **any state satisfying the invariant** and
//! any input (`proofs.rs`) then covers documents of every size.
//!
//! The states and steps, with their sources:
//!
//! - **Device pixels** (`geometry.rs`): `snap(v, scale)`: a length in 1/64
//!   CSS px to the nearest device pixel at `scale` device pixels per CSS
//!   pixel, half up. Contract: monotone (`a <= b` gives `snap(a) <=
//!   snap(b)`), exact on whole CSS pixels (`snap(64 * n) == n * scale`), and
//!   never overflows (it saturates at `i32`). `snap_rect(r, scale) ->
//!   DeviceRect`: each edge snapped on its own, so two rectangles that share
//!   an edge in CSS pixels share it in device pixels (no gap, no overlap).
//!   Contract: the width and height are the snapped right and bottom less
//!   the snapped left and top, never negative.
//! - **A colour** (`geometry.rs`): `premultiply(rgba) -> u32`: the
//!   premultiplied `0xAARRGGBB` that item 5.17a's list carries. Contract:
//!   each channel is at most the alpha; an opaque colour keeps its channels;
//!   a transparent one is 0.
//! - **A box's borders** (`geometry.rs`): `border_rects(box, widths)`: the
//!   four strips of a border box, top and bottom across its whole width,
//!   left and right between them (CSS 2.1 §8.5, every style drawn as
//!   `solid`). Contract: each strip lies inside the border box and no two
//!   overlap.
//! - **The clip** ([`Clips`], `order.rs`): the stack of `overflow` clips
//!   (§11.1.1) in force. The list carries at most one clip at a time, the
//!   intersection of the stack's rectangles, so item 5.17a's depth limit
//!   (256) is never reached however deep the clips nest. Steps:
//!   - `Clips::enter(self, rect) -> (Clips, ClipChange)`: a box's clip
//!     starts. Contract: the clip in force is the intersection of the one
//!     before and `rect`, so it lies within both; the change pops the old
//!     clip if there was one and pushes the new one; the depth grows by
//!     one.
//!   - `Clips::leave(self, outer) -> (Clips, ClipChange)`: it ends, `outer`
//!     being the clip in force before it. Contract: the depth shrinks by
//!     one; the change pops the clip and pushes `outer` back if there is
//!     one. Requires a depth above zero.
//!   - Invariant ([`Clips::invariant`]): a clip is in force exactly when
//!     the depth is above zero.
//! - **Text decorations** ([`Decor`], `decor.rs`), CSS 2.1 §16.3.1: the
//!   underline, overline and line-through affecting a box's text, each with
//!   the colour of the element that applies it. Steps:
//!   - `propagate(parent, own, colour, atomic, table_quirk) -> Decor`: a
//!     box's decorations from its parent's and its own `text-decoration`.
//!     Contract: an atomic inline (and, in quirks mode, a table: the Quirks
//!     Mode Standard's §3.11) starts from none ("nor to the contents of
//!     atomic inline-level descendants"); otherwise the parent's are kept;
//!     the box's own lines are added in its own colour, replacing the
//!     parent's colour for that line.
//!   - `line_rect(kind, baseline, metrics, x, width) -> Rect`: one
//!     decoration line under, over or through a run. Contract: its height is
//!     the thickness (at least 1/64 px) and it spans the run's width.
//!
//! The walk itself (`order.rs`, CSS 2.1 Appendix E.2) is a loop over an
//! explicit stack of tasks; its state is the fragment tree and the list.

use crate::flow::fragment::Rect;

/// A rectangle in device pixels, in document coordinates (the origin is the
/// initial containing block's top left corner; item 5.20 subtracts the
/// scroll position).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct DeviceRect {
    /// The left edge.
    pub x: i32,
    /// The top edge.
    pub y: i32,
    /// The width.
    pub width: u32,
    /// The height.
    pub height: u32,
}

impl DeviceRect {
    /// The right edge, in `i64`.
    pub fn right(&self) -> i64 {
        i64::from(self.x).saturating_add(i64::from(self.width))
    }

    /// The bottom edge, in `i64`.
    pub fn bottom(&self) -> i64 {
        i64::from(self.y).saturating_add(i64::from(self.height))
    }

    /// Whether it covers no pixel.
    pub fn is_empty(&self) -> bool {
        self.width == 0 || self.height == 0
    }
}

/// One glyph of a text item, at a position in 1/64 device pixel (so that
/// item 5.20 can pick the quarter-pixel mask item 5.17 makes for it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PlacedGlyph {
    /// The glyph id in the item's face.
    pub id: u16,
    /// Its origin's x, in 1/64 device pixel, document coordinates.
    pub x: i32,
    /// Its baseline's y, in 1/64 device pixel, document coordinates.
    pub y: i32,
}

/// The glyphs of one run in one face, size and colour.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextItem {
    /// The face, as [`crate::flow::TextFns`] numbers faces.
    pub face: u32,
    /// The size in 1/64 device pixel per em (the used font size times the
    /// scale).
    pub size: i32,
    /// Premultiplied `0xAARRGGBB`.
    pub colour: u32,
    /// The glyphs, in logical order.
    pub glyphs: Vec<PlacedGlyph>,
}

/// One item of the display list, in paint order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// Fill a rectangle: a background, a border strip, a decoration line,
    /// or the canvas.
    Fill {
        /// The rectangle.
        rect: DeviceRect,
        /// Premultiplied `0xAARRGGBB`.
        colour: u32,
    },
    /// Draw glyphs.
    Text {
        /// Where the glyphs may draw (for culling; see `order.rs`).
        bounds: DeviceRect,
        /// The glyphs.
        run: TextItem,
    },
    /// Clip what follows to a rectangle, until the next [`Item::PopClip`]
    /// (never nested: `Clips`).
    PushClip {
        /// The clip.
        rect: DeviceRect,
    },
    /// End the clip in force.
    PopClip,
}

impl Item {
    /// The device pixels the item may change, for item 5.20's culling
    /// (`None` for [`Item::PopClip`], which 5.20 keeps with its push).
    pub fn bounds(&self) -> Option<DeviceRect> {
        match self {
            Item::Fill { rect, .. } | Item::PushClip { rect } => Some(*rect),
            Item::Text { bounds, .. } => Some(*bounds),
            Item::PopClip => None,
        }
    }
}

/// Where a click goes: a link's fragment and its URL (item 5.18).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HitRegion {
    /// The fragment's rectangle.
    pub rect: DeviceRect,
    /// The link element (a DOM node id).
    pub node: usize,
    /// Its `href` parsed against the document's base URL and serialized
    /// (`None` when the URL parser fails: the link goes nowhere).
    pub url: Option<String>,
}

/// The display list of a document.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DisplayList {
    /// The items, in paint order (CSS 2.1 Appendix E.2).
    pub items: Vec<Item>,
    /// The hit regions, in paint order (a later one is on top).
    pub hits: Vec<HitRegion>,
    /// Device pixels per CSS pixel.
    pub scale: u32,
}

/// The clip stack's state (`order.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Clips {
    /// How many clips are in force.
    pub depth: u32,
    /// Their intersection, when there is one.
    pub current: Option<DeviceRect>,
}

impl Clips {
    /// No clip.
    pub const NONE: Clips = Clips {
        depth: 0,
        current: None,
    };

    /// The invariant: a clip is in force exactly when the depth is above
    /// zero.
    pub fn invariant(&self) -> bool {
        (self.depth > 0) == self.current.is_some()
    }
}

/// What a clip step emits: at most a pop and a push.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct ClipChange {
    /// Pop the clip in force first.
    pub pop: bool,
    /// Then push this one.
    pub push: Option<DeviceRect>,
}

/// The text decorations affecting a box's text (CSS 2.1 §16.3.1), each
/// with its colour (`clazel-style`'s `Rgba`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Decor {
    /// `underline`.
    pub underline: Option<[u8; 4]>,
    /// `overline`.
    pub overline: Option<[u8; 4]>,
    /// `line-through`.
    pub line_through: Option<[u8; 4]>,
}

/// Which decoration line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Line {
    /// Under the text.
    Underline,
    /// Over it.
    Overline,
    /// Through it.
    LineThrough,
}

/// A rectangle in 1/64 CSS px (the fragment tree's unit), re-exported for
/// the steps.
pub type CssRect = Rect;
