//! Table layout (phase-5.md item 5.15): the grid of a table box, its
//! column widths in the automatic and fixed algorithms, its row heights and
//! the vertical alignment of its cells, and the rectangles of its rows,
//! columns and their groups, for 5.14's walk (`flow/block.rs`) to place.
//!
//! # Sources
//!
//! - **CSS 2.1**, W3C Recommendation, 7 June 2011,
//!   <https://www.w3.org/TR/2011/REC-CSS2-20110607/tables.html>: §17.2 the
//!   table model (header and footer groups), §17.3 columns, §17.4 the table
//!   wrapper box and captions, §17.5 the grid, §17.5.2.1 "Fixed table
//!   layout", §17.5.2.2 "Automatic table layout" (non-normative), §17.5.3
//!   "Table height algorithms", §17.5.4 "Horizontal alignment in a column",
//!   §17.6.1 "The separated borders model". phase-5.md marks §17.3, §17.4
//!   and §17.5 with †; CSS 2.1's numbering is fixed, and each was checked
//!   against the Recommendation's text.
//! - **CSS Table Module Level 3**, Editor's Draft, the source
//!   `css-tables-3/Overview.bs` at w3c/csswg-drafts commit
//!   `e13fe879106ad83dd89faecab5edad868c7efbfa` (8 October 2026), SHA-256
//!   `e3497b67c34e5b22f497886fbc94a2424d4e3dc4afe2e5a55b662fe86c6e441d`,
//!   <https://drafts.csswg.org/css-tables-3/>. Section numbers were counted
//!   from that source's headings, and each citation also gives the
//!   heading's anchor: §3.2 `#table-layout-algorithm`; §3.3.1
//!   `#dimensioning-the-row-column-grid--step1` (HTML's algorithm on
//!   boxes); §3.3.2 `#dimensioning-the-row-column-grid--step2` ("Track
//!   merging"); §3.4 `#missing-cells-fixup`; §3.8.1
//!   `#computing-undistributable-space`; §3.8.2
//!   `#computing-cell-measures`; §3.8.3 `#computing-column-measures`
//!   ("computing column measures"); §3.9.1 `#computing-the-table-width`;
//!   §3.9.3 `#width-distribution-algorithm` ("distributing width to
//!   columns"), with §3.9.3.1 `#width-distribution-in-fixed-mode` and
//!   §3.9.3.2 `#distributing-width-to-columns`; §3.10.1
//!   `#computing-the-table-height`; §3.10.2 `#row-layout`; §3.10.5
//!   `#height-distribution-algorithm`; §3.11 `#bounding-box-assignment`.
//!   phase-5.md pins "CSS Tables Level 3 (Editor's Draft, pinned)"; this
//!   is the pin.
//! - **HTML**, commit `4c54fae106900a24130da614b7ad29d85c6981c6` (the one
//!   `clazel-style` vendors §15 from), the single source file with SHA-256
//!   `17d5541ac0f87fb8e9cba0ce19af64e9edc47563dd84fd779df188cd8f9aab4c`:
//!   §4.9.12 "Processing model", §4.9.12.1 "Forming a table" (with "the
//!   algorithm for processing row groups", "the algorithm for ending a row
//!   group", "the algorithm for processing rows" and "the algorithm for
//!   growing downward-growing cells"), which the plan calls "forming a
//!   table" (†; the number is the pinned source's); §2.3.4.2 "rules for
//!   parsing non-negative integers" (`clazel-style`'s `legacy.rs`); §15.3.8
//!   the user agent sheet's `table { box-sizing: border-box }`.
//! - **Quirks Mode Standard**, Living Standard, commit
//!   `5a06deb58ae2644d62c3c2026bbef86e6137b779` (5.14's pin): §3.8 "The
//!   table cell width calculation quirk", §3.9 "The table cell nowrap
//!   minimum width calculation quirk", §3.10 "The collapsing table quirk",
//!   §3.13 "The table cell height box sizing quirk". The plan's §3.8 to
//!   §3.10 (†) are the pinned text's.
//!
//! # The pipeline
//!
//! 1. `grid.rs`, once per table box before layout: HTML's "forming a table"
//!    over the box tree (CSS Tables 3 §3.3.1: boxes act as the HTML element
//!    their display type corresponds to), then §3.3.2's track merging. The
//!    result is each cell's slot and each row, column and group's tracks.
//! 2. `measure.rs`: each cell's outer min-content and max-content widths
//!    and percentage contribution (§3.8.2), from the content sizes 5.14's
//!    `intrinsic.rs` computes; each column's measures (§3.8.3), spanning
//!    cells by increasing span; the table's GRIDMIN and GRIDMAX, which
//!    `intrinsic.rs` uses as the table's own min-content and max-content
//!    widths, and its used width (§3.9.1), which `block.rs` gives the table
//!    wrapper box.
//! 3. `distribute.rs`: the column widths, by §3.9.3's sizing guesses (auto
//!    layout) or CSS 2.1 §17.5.2.1 (fixed layout), when the walk enters the
//!    table box; each cell is then laid out by 5.14's code, as a block
//!    formatting context root, at the width of the columns it spans.
//! 4. `rows.rs`, when the walk leaves the table box: each row's height and
//!    baseline (CSS 2.1 §17.5.3, CSS Tables 3 §3.10.2), the heights of
//!    cells spanning rows, the table's `height` (§3.10.5), and each cell's
//!    extra top and bottom padding for its `vertical-align`.
//! 5. `block.rs`, with these: every cell, row, row group, column and column
//!    group placed (§3.11), in the table box's content coordinates.
//!
//! `state.rs` states each state, its invariant and each step's contract; it
//! was committed before the implementation.
//!
//! # Modelling choices
//!
//! - **5.14's walk lays tables out**, and this module is functions over
//!   plain data: the walk enters a table box, asks for its column widths,
//!   lays each cell out with 5.14's block container code (a cell is a block
//!   formatting context root, §9.4.1), and on leaving the table asks for its
//!   rows. Nothing recurses: a table in a cell is entered by the same walk.
//! - **The grid is HTML's** (phase-5.md): CSS Tables 3 §3.3.1 has boxes act
//!   as the HTML element their display type corresponds to, using the
//!   attributes "of their originating element if and only if it is an HTML
//!   element of the same type", so `colspan` and `rowspan` count only on an
//!   HTML `td` or `th` that is a cell box, and `span` on an HTML `col` or
//!   `colgroup` that is a column or column group box.
//! - **Header and footer groups**: the first `table-header-group` is moved
//!   before the other row groups and the first `table-footer-group` after
//!   them (CSS 2.1 §17.2: "only the first is rendered as a header; the
//!   others are treated as if they had 'display: table-row-group'"); HTML's
//!   algorithm moves every `tfoot` to the end, but the boxes have display
//!   types, and CSS's rule is the one for display types.
//! - **Column groups after the first row** are skipped, as HTML's algorithm
//!   skips a `colgroup` that follows a row ("Rows: While the current element
//!   is not one of the following elements, advance"): their boxes are laid
//!   out empty. A `table-column` box directly in a table (only CSS can make
//!   one; HTML's parser puts every `col` in a `colgroup`) is a column group
//!   of its own.
//! - **Hostile input**: a grid has at most [`state::MAX_COLUMNS`] (65,536)
//!   columns. A cell or column that would start past the last column is
//!   placed in the last one, and one that would end past it is cut there,
//!   so every cell is laid out; the cells then overlap, which HTML's model
//!   allows ("It is possible, in certain error cases, for two cells to
//!   occupy the same slot") and CSS 2.1 §17.5 lets a user agent draw.
//!   Rows are counted in `u64` and are never visited one by one: a row
//!   group's implied rows (from `rowspan`) are reached in one step, and
//!   track merging removes them.
//! - **Track merging** (§3.3.2) merges a track into the one before it when
//!   no cell starts or ends between them and no box defines it: a column
//!   box (or a column group box with no columns, whose `span` makes the
//!   columns it stands for) defines its columns, a row box its row. Columns
//!   are merged only in auto layout ("For tables in fixed mode, only rows
//!   are eligible").
//! - **Missing cells** (§3.4) get no box: an anonymous cell would have no
//!   content, border or padding, and would change nothing that is laid out.
//! - **A table's `width` and `min-width` are its border box's** (HTML's
//!   user agent sheet has `table { box-sizing: border-box }`, and CSS 2.1
//!   §17.6.1: "in HTML and XHTML1, the width of the <table> element is the
//!   distance from the left border edge to the right border edge");
//!   `box-sizing` is not otherwise in the subset. `max-width` on a table is
//!   not applied: §3.9.1 does not read it. The table's `height` is its
//!   border box's too (a minimum, §3.10.1).
//! - **GRIDMIN, GRIDMAX and the assignable width include the table's
//!   borders and padding** (§3.8.2's "table intrinsic offsets"), which
//!   §3.9.1 compares with the border box width; read literally they leave
//!   them out (`docs/ERRATA.md`).
//! - **The width available to an auto-width table** is its containing
//!   block's width less its margins that are not `auto`, as CSS 2.1
//!   §10.3.5 has it for shrink-to-fit; §3.9.1 says "the table's containing
//!   block width", and CSS 2.1 §17.5.2 then applies §10.3's margin rules to
//!   the width found.
//! - **Spanning cells over columns with no max-content width**: §3.8.3's
//!   ratios of a column's max-content width to the "baseline max-content
//!   width" are undefined when that is zero; the contribution is then
//!   shared equally (`docs/ERRATA.md`), as §3.9.3.2 shares excess width
//!   among columns with no max-content width.
//! - **`min('max-width', 'width')`** in §3.8.2's outer max-content widths
//!   reads `width: auto` (and a percentage) as no width: the term is then
//!   left out, as `'width'` is in the formulas beside it.
//! - **A spanning cell's outer max-content width** uses §3.8.2's formula
//!   for "a constrained column" when the cell's own `width` is a length;
//!   constrainedness is defined per column, and a spanning cell is in
//!   several.
//! - **A column's max-content width is at least its min-content width**
//!   after each span step: §3.8.3's two contributions are rounded apart
//!   and could leave it 1/64 px below.
//! - **Fixed layout** (CSS 2.1 §17.5.2.1) applies when `table-layout` is
//!   `fixed` and `width` is not `auto` ("A value of 'auto' … means use the
//!   automatic table layout algorithm"). The first row is the grid's first
//!   row after the header group is moved; a first-row cell's width is its
//!   outer width (its `width` with its horizontal borders and padding); a
//!   percentage is of the assignable width; the "remaining columns" are
//!   every column neither a column box nor a first-row cell sizes; excess
//!   width follows §3.9.3.2's rules for fixed mode.
//! - **Percentage columns do not widen an auto-width table** past GRIDMAX:
//!   §3.9.1 does not count them, though engines do; to be checked against
//!   item 5.25's reference engine.
//! - **Row heights**: a row's minimum height is the largest of its row
//!   box's `height` (a length; a percentage counts as 0), the `height` of
//!   each cell spanning only that row, and what its cells need (CSS 2.1
//!   §17.5.3, CSS Tables 3 §3.10.2). A cell's `height` is its content box's,
//!   with its vertical borders and padding added, but its border box's in
//!   quirks mode (the Quirks Mode Standard's §3.13). Row groups' `height`
//!   is ignored (§3.10.2: "heights being defined on row groups are being
//!   ignored"). A cell spanning rows counts as height 0 in its first row
//!   (but with its baseline), then, by increasing span, any height its rows
//!   lack is shared among them in proportion to their heights (equally if
//!   all are 0): §3.10.2 says "the same algorithm as the column
//!   measurement", whose min-content contribution with one measure per row
//!   is that share.
//! - **The table's `height`** is a minimum (§3.10.1); the rows it adds are
//!   §3.10.5's: with no second pass (percentages count as 0), a row's
//!   reference size is its base size, and the extra goes equally to the
//!   "auto-height" rows (no row box `height` and no cell `height` on that
//!   row alone) if there are any, else to every row.
//! - **No second pass of cell content** (§3.10.6): a percentage height
//!   inside a cell is `auto`, as in the first pass.
//! - **`vertical-align`**: `baseline`, `top`, `middle`, `bottom`; every
//!   other value is `baseline` (§17.5.3). The space a cell does not fill is
//!   its extra top and bottom padding (§17.5.3: "Cell boxes that are
//!   smaller than the height of the row receive extra top or bottom
//!   padding"), so the fragment's padding includes it and its content box
//!   is where its content is.
//! - **Baselines** (§17.5.3): a cell's is its first line box's, as 5.14
//!   finds it (through nested blocks and tables), or the bottom of its
//!   content box; a table's is its first row's, or the bottom of its
//!   content box (§3.10.2); an inline table's is its table box's (§17.4).
//! - **Separated borders only.** Decision 5.0(b) takes the collapsing
//!   border model "if time allows"; it is not done here. A table with
//!   `border-collapse: collapse` is laid out with separated borders and no
//!   border spacing (listed). Rows, row groups, columns and column groups
//!   have no borders or padding in this model (§17.6.1: "user agents must
//!   ignore the border properties for those elements").
//! - **Captions** are above the table (`caption-side` is not in the
//!   subset, item 5.13), laid out as blocks in the wrapper, as wide as the
//!   table: CAPMIN widens the table (§3.9.1).
//! - **`visibility: collapse`** has no effect (CSS Tables 3 has it as an
//!   open issue, ISSUE 478); `empty-cells` is not in the subset.
//! - **A cell's percentage padding** is of the table box's content width.
//! - **The quirks** (quirks mode only): §3.8 (no soft wrap opportunity
//!   around an `img` in the min-content width of an auto-width cell's own
//!   inline formatting context), §3.9 (a `nowrap` cell's `width` as its
//!   minimum), §3.10 (an empty table's height and borders) and §3.13.

pub mod distribute;
pub mod grid;
pub mod measure;
pub mod rows;
pub mod state;

#[cfg(kani)]
mod proofs;
#[cfg(test)]
mod tests;

use clazel_style::cascade::computed::{ComputedStyle, Size};

use crate::boxes::{BoxId, BoxTree};

/// Whether table box `table` is laid out by CSS 2.1 §17.5.2.1's fixed
/// algorithm: its `table-layout` is `fixed` and its `width` (held by its
/// wrapper box, `flow/style.rs`) is not `auto` ("A value of 'auto' (for
/// both 'display: table' and 'display: inline-table') means use the
/// automatic table layout algorithm").
pub fn is_fixed(tree: &BoxTree, styles: &[ComputedStyle], table: BoxId) -> bool {
    let fixed = styles.get(table).is_some_and(|s| s.table_layout_fixed);
    let wrapper = tree.get(table).and_then(|t| t.parent);
    fixed
        && wrapper
            .and_then(|w| styles.get(w))
            .is_some_and(|s| !matches!(s.width, Size::Auto))
}
