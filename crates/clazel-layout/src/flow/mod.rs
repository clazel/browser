//! Block and inline formatting (phase-5.md item 5.14): from the box tree
//! (item 5.13), the computed style (item 5.7) and the fonts (items 5.10 and
//! 5.11) to a fragment tree: every box's position and size, and line boxes
//! with positioned glyph runs.
//!
//! # Sources
//!
//! - **CSS 2.1**, W3C Recommendation, 7 June 2011,
//!   <https://www.w3.org/TR/2011/REC-CSS2-20110607/>: §8.1 the box
//!   dimensions, §8.3.1 "Collapsing margins"; §9.4.1 "Block formatting
//!   contexts", §9.4.2 "Inline formatting contexts"; §10.1 the containing
//!   block; §10.3.1 to §10.3.4, §10.3.5 (the shrink-to-fit width), §10.3.9
//!   and §10.3.10 widths and margins; §10.4 `min-width` and `max-width`;
//!   §10.5 `height`; §10.6.1 to §10.6.3, §10.6.6 and §10.6.7 heights and
//!   margins; §10.7 `min-height` and `max-height`; §10.8 and §10.8.1 line
//!   height, leading and `vertical-align`; §16.1 `text-indent`; §16.2
//!   `text-align`; §17.4 the table wrapper box's margins. phase-5.md marks
//!   §10.3.2 to §10.3.9 and §10.6.3 and §10.6.7 with †; CSS 2.1's numbering
//!   is fixed, and each was checked against the Recommendation's text.
//! - **Quirks Mode Standard**, Living Standard last updated 19 October 2026,
//!   commit `5a06deb58ae2644d62c3c2026bbef86e6137b779`,
//!   <https://quirks.spec.whatwg.org/>: §3.3 "The line height calculation
//!   quirk", §3.4 "The blocks ignore line-height quirk", §3.5 "The
//!   percentage height calculation quirk", §3.6 "The html element fills the
//!   viewport quirk", §3.7 "The body element fills the html element quirk".
//!   The plan's numbers (§3.3, §3.4, §3.6, §3.7, all †) are the pinned
//!   text's.
//! - **HTML**, commit `4c54fae106900a24130da614b7ad29d85c6981c6` (the one
//!   `clazel-style` vendors §15 from): §15.2's "align descendants", which
//!   §15.3.3 (`center`, `div align`) and §15.3.8 (table parts' `align`) ask
//!   for and `clazel-style` passes as `align_descendants`; §15.4 and §15.5's
//!   sizes of replaced elements (item 5.13's `boxes/replaced.rs`).
//! - **CSS Text 3**, CRD of 14 August 2026: §4.1.2 Phase II and §5's line
//!   breaking through item 5.12's [`crate::text`]; §7.1†'s rule that a line
//!   whose content does not fit is start-aligned.
//!
//! # The pipeline
//!
//! [`layout`] runs, in order:
//!
//! 1. `style.rs`: every box's computed style: its node's, or for an
//!    anonymous box its parent box's inherited properties with the others
//!    initial (§9.2.1.1: "The properties of anonymous boxes are inherited
//!    from the enclosing non-anonymous box"), and §17.4's split of a table's
//!    properties between its wrapper and table boxes;
//! 2. `inline.rs`, preparation: each inline formatting context's units
//!    (item 5.12's Phase I output, gathered from its text runs and atomic
//!    inlines), their wrap opportunities, and each text run shaped once;
//! 3. `intrinsic.rs`: the min-content and max-content widths that
//!    shrink-to-fit (§10.3.5) reads, in one pass from the leaves up;
//! 4. `block.rs`: the walk, with an explicit stack: widths top down
//!    (`widths.rs`), the block flow with margin collapsing
//!    (`margins.rs`), line boxes (`inline.rs`) and heights bottom up
//!    (`heights.rs`);
//! 5. `block.rs`: positions from relative to absolute, top down.
//!
//! # Modelling choices
//!
//! Each file lists its own; these are the ones that cross files.
//!
//! - **Fonts are a parameter**, [`fonts::TextFns`], as computed style is for
//!   the box tree (item 5.13's `StyleFns`): the metrics of an element's first
//!   available font and the shaping of a run. [`fonts::FaceFonts`] is the
//!   real one, over `clazel-font` faces with item 5.10's matching and item
//!   5.11's shaper; [`fonts::BoxFont`] gives every glyph an em square, with
//!   the metrics of WPT's Ahem font, so that tests can be checked by hand.
//! - **Only what the subset has**: no floats, no positioning, no clearance
//!   (decision 5.0(b) A), so every box is in flow, line boxes are as wide
//!   as their containing block, and §8.3.1's clearance clauses never apply.
//!   `direction` is `ltr` and the writing mode horizontal.
//! - **Content that does not fit overflows** (phase-5.md); `overflow:
//!   hidden` makes a block formatting context here and clips in item 5.16.
//! - **Tables are item 5.15's.** Until then their boxes have this
//!   placeholder layout, which keeps every box in them laid out and their
//!   text readable: a table wrapper box is laid out as a block box with the
//!   table element's margins and `width` (shrink-to-fit when `auto`, as an
//!   inline block would be); the table box as a block box filling it, with
//!   the table's borders and padding; row groups, rows, cells and captions
//!   as block boxes in their parent's flow, in tree order, one below the
//!   other, each cell and caption a block formatting context root (as §9.4.1
//!   says they are); columns and column groups as empty boxes at their
//!   parent's top. `border-spacing`, column widths, cell `vertical-align`
//!   and `colspan` have no effect yet.
//! - **A list item's marker** (item 5.13: always `outside`, its list item's
//!   first child) is laid out as a line of its own text in the list item's
//!   font, ending at the list item's content edge (the marker text's suffix,
//!   ". " or a space, is the gap), on the list item's first baseline, or
//!   with its top at the list item's content top when there is no line.
//! - **Positions** are computed relative to the parent box's content box
//!   while laying out, and made absolute in one last pass.
//! - **The whole document is laid out again** for a new viewport
//!   (phase-5.md): [`layout`] is a function of its inputs.

pub mod block;
pub mod dump;
pub mod fonts;
pub mod fragment;
pub mod heights;
pub mod inline;
pub mod intrinsic;
pub mod length;
pub mod margins;
pub mod replaced;
pub mod state;
pub mod style;
pub mod widths;


pub use block::Mode;
pub use fonts::{BoxFont, FaceFonts, FontMetrics, ShapedGlyph, TextFns};
pub use fragment::{
    BoxFragment, FragmentTree, Glyph, GlyphRun, InlinePiece, LineBox, LineItem, Rect, Sides,
};

use clazel_dom::exec::Arena;

use crate::boxes::{BoxTree, StyleFns};

/// The viewport: the size of the initial containing block (CSS 2.1 §10.1),
/// in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Viewport {
    /// Its width.
    pub width: i32,
    /// Its height.
    pub height: i32,
}

impl Viewport {
    /// A viewport of `width` by `height` CSS pixels.
    pub fn px(width: u16, height: u16) -> Viewport {
        Viewport {
            width: i32::from(width).saturating_mul(64),
            height: i32::from(height).saturating_mul(64),
        }
    }
}

/// The fragment tree of box tree `tree`, built from the document in
/// `arena` (whose mode decides the quirks) with computed style `styles`,
/// in fonts `fonts`, for a viewport of size `viewport` (the module's
/// pipeline).
pub fn layout(
    tree: &BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    fonts: &impl TextFns,
    viewport: Viewport,
) -> FragmentTree {
    block::run(tree, arena, styles, fonts, viewport)
}
