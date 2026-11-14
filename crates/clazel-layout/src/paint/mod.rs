//! Paint (phase-5.md item 5.16): from the fragment tree (items 5.14 and
//! 5.15) to a display list, a flat list of items in paint order, each with
//! integer device-pixel bounds, and the hit regions of links.
//!
//! # Sources
//!
//! - **CSS 2.1**, W3C Recommendation, 7 June 2011,
//!   <https://www.w3.org/TR/2011/REC-CSS2-20110607/>: Appendix E.2
//!   "Painting order" (`zindex.html`), whose list is numbered here as it
//!   nests: step 1 (the root's background over the canvas), 2 (a block's or
//!   table's own background and borders), 3 (negative stacking contexts), 4
//!   (every in-flow block-level descendant's background and borders, a
//!   table's in its six layers), 5 (floats), 6 (an inline stacking context),
//!   7 (the inline content: 7.1 block-level replaced content; 7.2 each line
//!   box, with 7.2.1 each box in it: 7.2.1.1 to 7.2.1.3 its background and
//!   border, 7.2.1.4 for an inline element its text runs, with 7.2.1.4.1
//!   underline, overline, the text, line-through, and its inline children
//!   by 7.2.1 again; 7.2.1.5 inline blocks and inline tables as if they made
//!   a stacking context; 7.2.1.6 inline replaced content), 8 to 10
//!   (positioned descendants and outlines); §14.2 "The background" (the
//!   root's and `body`'s background propagated to the canvas); §8.5 "Border
//!   properties"; §16.3.1 `text-decoration`; §11.1 and §11.1.1 `overflow`
//!   ("whether a box is clipped to its padding edge"); §11.2 `visibility`;
//!   §17.5.1 "Table layers and transparency"; §17.6.1 (no row, column or
//!   group backgrounds in the border spacing). phase-5.md marks E.2, §14.2,
//!   §8.5, §16.3.1 and §11.1.1 with †; CSS 2.1's numbering is fixed, and
//!   each was checked against the Recommendation's text.
//! - **HTML**, commit `4c54fae106900a24130da614b7ad29d85c6981c6`: §4.6.2
//!   "Links created by a and area elements" ("when those elements do not
//!   have href attributes they do not create hyperlinks") and §4.6.4
//!   "Following hyperlinks" ("Let urlRecord be the result of
//!   encoding-parsing a URL given subject's href attribute value, relative
//!   to subject's node document. If urlRecord is failure, then return.").
//! - **URL**, through `clazel-url`'s basic URL parser and serializer.
//! - **Quirks Mode Standard**, commit `5a06deb5` (5.14's pin): §3.11 "The
//!   text decoration doesn't propagate into tables quirk".
//! - **Item 5.17a's display list** (`clazel-displaylist`), which this list
//!   becomes in item 5.20: its rectangles, clips and premultiplied colours.
//!
//! # The pipeline
//!
//! [`paint`] runs `order.rs`'s walk over the fragment tree, in E.2's order
//! for the root stacking context, which is the only one the subset makes:
//! the canvas (step 1), every block-level box's background and borders in
//! tree order (steps 2 and 4), then every block container's line boxes in
//! tree order (step 7), each atomic inline painted whole at its place in its
//! line (7.2.1.5). `geometry.rs` snaps rectangles to device pixels and
//! premultiplies colours; `decor.rs` carries text decorations down the tree
//! and places their lines; `dump.rs` prints a list for the tests.
//!
//! `state.rs` states each state, its invariant and each step's contract; it
//! was committed before the implementation.
//!
//! # Modelling choices
//!
//! - **Its own list, which item 5.20 converts.** Item 5.17a's list
//!   (`clazel-displaylist`) holds device-pixel rectangles, clips and glyph
//!   masks in viewport coordinates, and nothing about text or links: the
//!   masks are made from glyphs by item 5.17 in 5.20's pipeline, and the
//!   viewport moves with every scroll. So this module produces [`Item`]s in
//!   document coordinates, already in device pixels with premultiplied
//!   colours, which 5.20 culls to the viewport, offsets by the scroll and
//!   writes as `FillRect`, `PushClip`, `PopClip` and, for a text item's
//!   glyphs, `UploadMask` and `DrawMask`. `clazel-displaylist`'s proven spec
//!   is not changed. A scroll draws again without a relayout, as the plan
//!   asks.
//! - **E.2 as written, not its paraphrase.** phase-5.md summarises the
//!   order as "for each block … its background and borders, then its
//!   in-flow blocks, then its inline content". E.2's steps 4 and 7 paint
//!   *every* block's background and borders before *any* line box, so text
//!   is never covered by a later block's background (Hacker News'
//!   `margin-bottom: -10px` overlaps blocks); E.2 is followed.
//! - **Within a line**, the backgrounds and borders of its inline box
//!   pieces come first, in tree order, then its text and atomic inlines in
//!   content order (5.14's line items are in that order). E.2's 7.2.1 paints
//!   an inline box's background just before its own content, so the two
//!   differ only where an inline box's background overlaps text earlier on
//!   the same line (negative margins); listed.
//! - **The canvas** is filled over the document's extent (the fragment
//!   tree's, which covers the viewport) with the root element's background,
//!   or, when that is transparent and the root is an `html` element, its
//!   first `body` child's (§14.2), which then paints no background of its
//!   own. When both are transparent the canvas is opaque white (E.2: "given
//!   a UA-defined color").
//! - **Borders are solid** whatever their style (phase-5.md: "every style
//!   drawn as `solid`, listed"): four strips, top and bottom across the
//!   border box, left and right between them; corners belong to the top
//!   and bottom strips (CSS draws a diagonal join between two colours).
//!   `none` and `hidden` have width 0 already (computed values).
//! - **Backgrounds** are `background-color` only (`background-image` is
//!   parsed and not applied, item 5.6), painted over the border box (§14.2:
//!   "the content, padding and border areas").
//! - **Tables** (E.2 step 4's table layers, §17.5.1): the table's
//!   background, then for each layer (column groups, columns, row groups,
//!   rows) the background of each cell's track over that cell (§17.6.1: no
//!   track background shows in the border spacing; a cell takes its row's
//!   and row group's from its parent row and its column's and column
//!   group's from the column it starts in), then the cells' backgrounds,
//!   then the table's and the cells' borders in tree order. Captions are
//!   blocks.
//! - **`visibility`** other than `visible` paints nothing of the box itself
//!   (its background, borders, text and decorations), and its descendants
//!   paint as their own `visibility` says (§11.2: "Descendants of the
//!   element will be visible if they have 'visibility: visible'"); it is
//!   still laid out.
//! - **`overflow`** other than `visible` clips the box's content (its
//!   descendants' backgrounds, borders and lines) to its padding box
//!   (§11.1), except on the root element and on a `body` whose `overflow` is
//!   propagated to the viewport (§11.1.1), whose clip is the viewport's
//!   (item 5.20). `scroll` and `auto` give no scrolling mechanism and clip
//!   as `hidden`. Clips never nest in the list: [`state::Clips`] emits the
//!   intersection of the clips in force, so 5.17a's depth limit holds.
//! - **Text decorations** (§16.3.1): each box carries the lines in force
//!   for its text with the colour of the element applying them; a deeper
//!   element's line of the same kind replaces an outer one's (E.2 paints the
//!   deepest topmost, at the same position, so only its colour shows). The
//!   position and thickness are the run's own font's (§16.3.1 allows "the
//!   font sizes … of descendants"): the underline at the `post` table's
//!   `underlinePosition` and `underlineThickness` (phase-5.md), the overline
//!   at the top of the run's ascent, the line-through centred half the
//!   x-height above the baseline, both as thick as the underline. A line is
//!   at least one device pixel thick. Decorations do not reach atomic
//!   inlines' contents, nor, in quirks mode, tables (§3.11).
//! - **Text items' bounds**, for culling, are the run's pen extent widened
//!   by its font size on each side and from two font sizes above the
//!   baseline to one below, so that no glyph ink overhanging its advance is
//!   culled; the glyphs keep their exact 1/64 px positions (times the scale).
//! - **Replaced boxes paint nothing** (phase-5.md: the image item is Phase
//!   6's); their backgrounds and borders are painted as any box's.
//! - **Hit regions**: every box inside a link (the nearest `a` or `area`
//!   ancestor-or-self with an `href`), laid out as a box, gives its border
//!   box, and every inline box piece its background rectangle, in paint
//!   order; a box whose `visibility` is not `visible` gives none. The URL
//!   is the `href` parsed by the basic URL parser against the
//!   document's base URL, which the caller gives (item 5.20 knows the
//!   document's URL and `base` element), and serialized; HTML's
//!   "encoding-parsing" uses the document's encoding for the query, which is
//!   UTF-8 here (listed). A link whose URL fails gets a region with no URL.
//! - **Device pixels**: an integer number of device pixels per CSS pixel,
//!   from 1 to 16 (a fractional device pixel ratio is item 5.21's to
//!   decide); every edge is snapped on its own, half up. Rectangles are not
//!   clamped to item 5.17a's coordinate range: 5.20 subtracts the scroll
//!   first, then clamps.
//! - **No item cap here**: 5.17a's limit of 1,048,576 items per list applies
//!   to what 5.20 sends for one viewport, after culling.

pub mod decor;
pub mod dump;
pub mod geometry;
pub mod order;
pub mod state;

#[cfg(kani)]
mod proofs;
#[cfg(test)]
mod tests;

pub use order::paint;
pub use state::{DeviceRect, DisplayList, HitRegion, Item, PlacedGlyph, TextItem};
