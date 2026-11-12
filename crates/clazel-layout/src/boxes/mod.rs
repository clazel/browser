//! The box tree (phase-5.md item 5.13): from the DOM and each element's
//! computed style to a tree of boxes in an arena, which block, inline and
//! table formatting (items 5.14 and 5.15) lay out and paint (item 5.16)
//! draws.
//!
//! # Sources
//!
//! - **CSS 2.1**, W3C Recommendation, 7 June 2011,
//!   <https://www.w3.org/TR/2011/REC-CSS2-20110607/>: §9.2 "Controlling box
//!   generation" (§9.2.1 block-level boxes, §9.2.1.1 anonymous block boxes,
//!   §9.2.2 inline-level boxes, §9.2.2.1 anonymous inline boxes, §9.2.4
//!   `display`), §9.7 (`display`, `position` and `float`), §12.5 "Lists",
//!   §17.2 "The CSS table model" with §17.2.1 "Anonymous table objects",
//!   and §17.4 (the table wrapper box). phase-5.md marks these numbers †;
//!   they are CSS 2.1's, whose numbering is fixed, and were checked against
//!   that text.
//! - **CSS Display 3**† (`display: none`, `contents`, root blockification),
//!   **CSS Lists 3**† and **CSS Counter Styles 3**† (`marker.rs`), cited
//!   from their current drafts, not a pinned commit (phase-5.md's †
//!   convention).
//! - **CSS Text 3**, CRD of 14 August 2026: §4.1.1 Phase I, through item
//!   5.12's [`crate::text::collapse`].
//! - **HTML** at commit `4c54fae106900a24130da614b7ad29d85c6981c6`: §15.3.4
//!   (`br`, `wbr`), §15.3.7 (lists), §15.4 and §15.5 (replaced elements,
//!   `replaced.rs`).
//!
//! # The pipeline
//!
//! [`build`] runs, in order:
//!
//! 1. [`generate::generate`]: every node's principal box and additional
//!    boxes (§9.2, §9.7, `none` and `contents`, list markers, replaced
//!    elements, `br` and `wbr`), with text nodes as text runs, walking the
//!    DOM iteratively;
//! 2. [`table::anonymous_table_objects`]: §17.2.1's three stages (remove
//!    irrelevant boxes, generate missing child wrappers, generate missing
//!    parents), then §17.4's table wrapper boxes;
//! 3. [`anonymous::split_blocks`]: §9.2.1.1's anonymous block boxes, with
//!    inline boxes that hold block-level boxes split around them;
//! 4. [`anonymous::text_runs`]: Phase I over each inline formatting
//!    context, and §9.2.2.1's removal of the white space it collapses away;
//! 5. [`tree::BoxTree::compact`]: the boxes renumbered in tree order.
//!
//! # Input
//!
//! Computed style is a parameter, [`StyleFns`] (phase-5.md: "a function
//! from node id to the subset's computed values"), so this module and items
//! 5.14 to 5.16 can be tested with hand-written tables;
//! `clazel_style::cascade::ComputedTable`, item 5.7's output, implements it.
//!
//! # Modelling choices
//!
//! Each file lists its own; these are the ones that cross files.
//!
//! - **Not in the subset, so not here**: `position` and `float` (every box
//!   is in flow, §9.7 is the identity), `display: contents` (only through
//!   [`StyleFns::display_contents`]), `list-style-position`, counters,
//!   `caption-side`, `::before` and `::after` (decision 5.0(b) takes them
//!   only "if time allows"), `display: run-in` (not in CSS 2.1's
//!   Recommendation either) and the CSS Display 3 values the subset lacks
//!   (`flow-root`, `flex`, `grid`, `ruby`).
//! - **Order of the passes.** §17.2.1 runs before §9.2.1.1, so that a
//!   table-internal box in a block (wrapped in an anonymous table, a
//!   block-level box) gets the anonymous blocks that box needs, and the
//!   anonymous cells of stage 2 are block containers whose content
//!   §9.2.1.1 then sorts out. Phase I runs last, on the final inline
//!   formatting contexts, since collapsing crosses inline boundaries.
//! - **Every pass is iterative**, with explicit stacks, so a document of any
//!   depth builds without recursion; each pass is a loop over a step whose
//!   state is small (`state.rs`), and the Kani harnesses (`proofs.rs`) take
//!   any state satisfying its invariant.
//! - **Anonymous boxes store no style**; their inherited properties come
//!   from the nearest ancestor box with a node, the others are initial
//!   (§9.2.1.1, §9.2.2.1, §17.2.1's "anonymous objects"), which layout
//!   applies.

pub mod anonymous;
pub mod dump;
pub mod generate;
pub mod marker;
pub mod replaced;
pub mod state;
pub mod table;
pub mod tree;

#[cfg(test)]
mod tests;

pub use replaced::{Input, Replaced};
pub use tree::{BoxId, BoxKind, BoxTree, Class, Fragment, LayoutBox, Marker, RowGroup, TextRun};

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::{ComputedStyle, ComputedTable};

/// Computed style as box generation reads it: for each node id, the
/// element's computed values for the subset, or `None` for a node that is
/// not an element or has no style (an element in a `template`'s contents).
pub trait StyleFns {
    /// The computed style of element `node`.
    fn style(&self, node: usize) -> Option<&ComputedStyle>;

    /// Whether element `node` has `display: contents` (CSS Display 3
    /// §2.5†), which the subset does not compute; `false` unless a
    /// hand-written table says otherwise.
    fn display_contents(&self, node: usize) -> bool {
        let _ = node;
        false
    }
}

impl StyleFns for ComputedTable {
    fn style(&self, node: usize) -> Option<&ComputedStyle> {
        self.get(node)
    }
}

/// The box tree of the document in `arena` with the computed style
/// `styles` (the module's pipeline).
pub fn build(arena: &Arena, styles: &impl StyleFns) -> BoxTree {
    let mut tree = generate::generate(arena, styles);
    table::anonymous_table_objects(&mut tree);
    anonymous::split_blocks(&mut tree);
    anonymous::text_runs(&mut tree, arena, styles);
    tree.compact();
    tree
}
