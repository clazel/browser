//! The states of table layout, their invariants, and the contracts of the
//! steps over them (phase-5.md item 5.15).
//!
//! As in `flow/state.rs`, every loop of table layout is a fold of a step
//! function over a small state: the state's invariant is written here as a
//! function, and each step's contract says what it keeps and what it
//! establishes. A Kani harness over **any state satisfying the invariant**
//! and any input (`proofs.rs`) then covers tables of every size: each state
//! starts satisfying its invariant, every step keeps it, so no step on any
//! table can panic or overflow or break the properties its harness asserts.
//!
//! The states and steps, with their sources:
//!
//! - **Forming a table** ([`Former`]): HTML §4.9.12.1's variables
//!   *xwidth*, *yheight*, *xcurrent* and *ycurrent*. Steps (`grid.rs`):
//!   - `spans(colspan, rowspan) -> Spans`: the "processing rows" steps that
//!     parse and clamp a cell's `colspan` ("If parsing that value failed, or
//!     returned zero, or if the attribute is absent, then let colspan be 1,
//!     instead. If colspan is greater than 1000, let it be 1000 instead.")
//!     and `rowspan` ("If parsing that value failed or if the attribute is
//!     absent, then let rowspan be 1, instead. If rowspan is greater than
//!     65534, let it be 65534 instead." … "If rowspan is zero, then set cell
//!     grows downward to true and set rowspan to 1"). Contract: `colspan` in
//!     `1..=1000`, `rowspan` in `1..=65534`, `downward` exactly when the
//!     parsed `rowspan` was zero.
//!   - `start_row(f) -> Former`: "If yheight is equal to ycurrent, then
//!     increase yheight by 1" and "Let xcurrent be 0". Contract: the
//!     invariant is kept, `xcurrent` is zero and the current row exists
//!     (`ycurrent < yheight`).
//!   - `place(f, free, spans) -> (Placed, Former)`: from "If xcurrent is
//!     equal to xwidth, increase xwidth by 1" to "Increase xcurrent by
//!     colspan", where `free` is the first column at or after `xcurrent`
//!     whose slot in the current row has no cell (the "Cells" step's loop,
//!     which the driver runs over its record of covered slots). Requires
//!     the current row to exist and `xcurrent <= free <= xwidth`. Contract:
//!     the invariant is kept; the cell is anchored at `(free, ycurrent)`
//!     (at the last column when the grid is full, [`MAX_COLUMNS`]) and lies
//!     inside the grid (`x + width <= xwidth`, `y + height <= yheight`);
//!     `xcurrent` moves to the cell's right edge.
//!   - `end_row(f)`: "increase ycurrent by 1". Contract: the invariant is
//!     kept (the current row existed, so `ycurrent <= yheight` after).
//!   - `end_group(f)`: "the algorithm for ending a row group": "While
//!     ycurrent is less than yheight … Increase ycurrent by 1", done in one
//!     step (the downward-growing cells are grown to `yheight` by the
//!     driver). Contract: `ycurrent == yheight`, the invariant kept.
//! - **A share of a length among weights** ([`Share`]): every "increased in
//!   proportion to …" and "linear combination" of CSS Tables 3 §3.8.3 and
//!   §3.9.3, and the row height distributions. Rounding each share on its
//!   own would lose or invent 1/64 px; instead the shares are the
//!   differences of the running total's floor, `floor(total · seen /
//!   weights)`, so they add up to exactly `total` (CSS Tables 3's Rule 3,
//!   "The sum of width assigned to all columns should be equal to the
//!   assignable table width"). Steps (`distribute.rs`):
//!   - `Share::new(total, weights)`: requires `total >= 0` and `0 <
//!     weights <= MAX_WEIGHTS` (2^31). Contract: the invariant holds.
//!   - `share_step(s, w) -> (piece, Share)`: the next weight `w`. Requires
//!     `0 <= w <= weights - seen`. Contract: the invariant is kept; the
//!     piece is not negative; `given` grows by `piece`; the piece is at
//!     most `w` when `total` is at most `weights` (an interpolation never
//!     passes its upper guess); and once every weight has been seen (`seen
//!     == weights`), `given == total`.
//! - **A column's measures** ([`Measure`]), CSS Tables 3 §3.8.3: its
//!   min-content width, max-content width and intrinsic percentage width.
//!   Steps (`measure.rs`):
//!   - `widen(m, min, max, pct) -> Measure`: "the largest of" each measure
//!     and a contribution. Contract: the invariant is kept, no measure
//!     decreases, each is at least its contribution (negative contributions
//!     count as zero, percentages above 100% as 100%).
//!   - `cell_outer(content, sizes) -> Measure`: §3.8.2's outer min-content
//!     and max-content widths and percentage contribution of a cell.
//!     Contract: the invariant holds; the min-content width is at least the
//!     cell's intrinsic offsets.
//! - **The used width of a table** ([`TableWidthInput`]), CSS Tables 3
//!   §3.9.1 (`measure.rs`): `used_width(input) -> i32`. Contract: the
//!   result is the used min-width (the largest of `min-width`, CAPMIN and
//!   GRIDMIN) or more; with a `width` it is the larger of that width and
//!   the used min-width, and with `width: auto` the larger of
//!   `min(GRIDMAX, available)` and the used min-width.
//! - **A row's vertical extent** ([`RowExtent`]), CSS 2.1 §17.5.3 and CSS
//!   Tables 3 §3.10.2: the cells aligned on the baseline set the row's
//!   baseline (the largest distance from a cell's top to its baseline) and
//!   what lies below it; the others need only fit. Steps (`rows.rs`):
//!   - `add_baseline(r, above, below)`: a cell aligned on its baseline,
//!     `above` its top-to-baseline distance and `below` the rest of its
//!     height. Contract: the invariant is kept; the extent covers the cell.
//!   - `add_other(r, height)`: a cell aligned at the top, middle or bottom.
//!     Contract: the invariant is kept; the height is at least `height`.
//!   - `row_height(r, specified) -> i32`: the row's height. Contract: at
//!     least `specified`, every cell's height, and `above + below`.
//! - **A cell's place in its rows** (`rows.rs`): `cell_offsets(align, span,
//!   baseline, height, cell_baseline) -> (top, bottom)`: the extra top and
//!   bottom padding (CSS 2.1 §17.5.3: "Cell boxes that are smaller than the
//!   height of the row receive extra top or bottom padding"). Contract: both
//!   are at least zero and `top + height + bottom` is the larger of the
//!   rows' height and the cell's.
//! - **What each box is to the walk** (`flow/state.rs`'s [`Role`], extended
//!   for this item): a table cell is [`Role::Cell`], laid out as a block
//!   formatting context root at the width its columns give it by 5.14's
//!   code; row groups and rows are [`Role::Track`] and columns and column
//!   groups [`Role::Column`], placed by their table; the table box and
//!   captions stay in their wrapper's flow.
//!
//! [`Role`]: crate::flow::state::Role
//! [`Role::Cell`]: crate::flow::state::Role
//! [`Role::Track`]: crate::flow::state::Role
//! [`Role::Column`]: crate::flow::state::Role

/// 100%, in the unit percentages have here: millionths of a percent
/// (`clazel-style`'s `Num::millionths` of a `<percentage>`).
pub const HUNDRED: i64 = 100_000_000;

/// HTML §4.9.12.1: "If colspan is greater than 1000, let it be 1000
/// instead."
pub const MAX_COLSPAN: u32 = 1000;

/// HTML §4.9.12.1: "If rowspan is greater than 65534, let it be 65534
/// instead."
pub const MAX_ROWSPAN: u32 = 65534;

/// The most columns a table's grid has (`mod.rs`, hostile input): HTML's
/// algorithm has no bound, and `<col span=1000>` makes a thousand columns
/// from fifteen bytes.
pub const MAX_COLUMNS: u32 = 1 << 16;

/// HTML §4.9.12.1's variables while forming a table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Former {
    /// *xwidth*: the number of columns so far.
    pub xwidth: u32,
    /// *yheight*: the number of rows so far.
    pub yheight: u64,
    /// *xcurrent*.
    pub xcurrent: u32,
    /// *ycurrent*.
    pub ycurrent: u64,
}

impl Former {
    /// "Let xwidth be 0. Let yheight be 0." with *xcurrent* and *ycurrent*
    /// zero.
    pub const START: Former = Former {
        xwidth: 0,
        yheight: 0,
        xcurrent: 0,
        ycurrent: 0,
    };

    /// The invariant: "xcurrent is never greater than xwidth" and
    /// "ycurrent is never greater than yheight" (the algorithm's own
    /// notes), and the grid has at most [`MAX_COLUMNS`] columns.
    pub fn invariant(&self) -> bool {
        self.xcurrent <= self.xwidth && self.xwidth <= MAX_COLUMNS && self.ycurrent <= self.yheight
    }
}

/// A cell's `colspan` and `rowspan` after HTML §4.9.12.1's parsing and
/// clamping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Spans {
    /// *colspan*, `1..=1000`.
    pub colspan: u32,
    /// *rowspan*, `1..=65534`.
    pub rowspan: u32,
    /// *cell grows downward*.
    pub downward: bool,
}

/// Where a cell was placed, in HTML's coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Placed {
    /// *cellx*.
    pub x: u32,
    /// *celly*.
    pub y: u64,
    /// Its width (*colspan*, less what the column bound cut).
    pub width: u32,
    /// Its height (*rowspan*).
    pub height: u32,
}

/// The largest sum of weights a [`Share`] takes: with it, every product
/// [`floor_share`] forms fits in an `i64` (`distribute.rs` scales larger
/// weights down).
pub const MAX_WEIGHTS: i64 = 1 << 31;

/// `floor(total * seen / weights)` for `total >= 0`, `0 <= seen <= weights`
/// and `0 < weights <= MAX_WEIGHTS`, without forming the product: with
/// `total = q * weights + r` (`0 <= r < weights`), it is `q * seen +
/// floor(r * seen / weights)`, where `q * seen <= total` and `r * seen <
/// 2^62`.
pub fn floor_share(total: i64, seen: i64, weights: i64) -> i64 {
    let q = total.checked_div(weights).unwrap_or(0);
    let r = total.checked_rem(weights).unwrap_or(0);
    let rest = r.saturating_mul(seen).checked_div(weights).unwrap_or(0);
    q.saturating_mul(seen).saturating_add(rest)
}

/// A running share of `total` among weights adding up to `weights`
/// (`distribute.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Share {
    /// What is shared out.
    pub total: i64,
    /// The sum of all the weights.
    pub weights: i64,
    /// The sum of the weights seen so far.
    pub seen: i64,
    /// What has been given out so far.
    pub given: i64,
}

impl Share {
    /// The invariant: the total is not negative, the weights are positive
    /// and at most [`MAX_WEIGHTS`], the weights seen are within them, and
    /// what was given is the floor of the total's share for the weights seen,
    /// `floor(total * seen / weights)` ([`floor_share`]).
    pub fn invariant(&self) -> bool {
        if self.total < 0
            || self.weights <= 0
            || self.weights > MAX_WEIGHTS
            || self.seen < 0
            || self.seen > self.weights
        {
            return false;
        }
        self.given == floor_share(self.total, self.seen, self.weights)
    }
}

/// A column's measures (CSS Tables 3 §3.8.3), or a cell's outer ones
/// (§3.8.2), in 1/64 px and millionths of a percent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Measure {
    /// The min-content width.
    pub min: i32,
    /// The max-content width.
    pub max: i32,
    /// The intrinsic percentage width (a percentage contribution, for a
    /// cell).
    pub pct: i64,
}

impl Measure {
    /// The invariant: `0 <= min <= max` and `0 <= pct <= 100%`.
    pub fn invariant(&self) -> bool {
        self.min >= 0 && self.min <= self.max && self.pct >= 0 && self.pct <= HUNDRED
    }
}

/// What CSS Tables 3 §3.9.1 reads to compute a table's used width, in
/// 1/64 px; every width is the table's border box (`mod.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct TableWidthInput {
    /// GRIDMIN: the columns' min-content widths, the border spacing and the
    /// table's horizontal borders and padding.
    pub gridmin: i32,
    /// GRIDMAX: likewise with the max-content widths.
    pub gridmax: i32,
    /// CAPMIN: the largest min-content contribution of a caption.
    pub capmin: i32,
    /// The resolved `min-width` (zero for `auto`).
    pub min_width: i32,
    /// The resolved `width`, `None` for `auto`.
    pub width: Option<i32>,
    /// The width available in the containing block.
    pub available: i32,
}

/// A row's vertical extent so far (CSS 2.1 §17.5.3), from its top.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct RowExtent {
    /// The largest distance from the top of a cell aligned on its baseline
    /// to its baseline: the row's baseline.
    pub above: i32,
    /// The largest distance from that baseline to the bottom of such a
    /// cell.
    pub below: i32,
    /// The provisional height: the lowest bottom of every cell so far.
    pub height: i32,
    /// Some cell is aligned on its baseline.
    pub baseline: bool,
}

impl RowExtent {
    /// No cell yet.
    pub const EMPTY: RowExtent = RowExtent {
        above: 0,
        below: 0,
        height: 0,
        baseline: false,
    };

    /// The invariant: every length is at least zero, the height covers the
    /// baseline-aligned cells (`above + below`, saturating), and a row
    /// without such a cell has no baseline extent.
    pub fn invariant(&self) -> bool {
        self.above >= 0
            && self.below >= 0
            && self.height >= self.above.saturating_add(self.below)
            && (self.baseline || (self.above == 0 && self.below == 0))
    }
}

/// How a cell is aligned in its rows (CSS 2.1 §17.5.3, CSS Tables 3
/// §3.10.2): "Other values do not apply to cells; the cell is aligned at
/// the baseline instead."
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum CellAlign {
    /// `baseline` (and every value that does not apply to cells).
    Baseline,
    /// `top`.
    Top,
    /// `middle`.
    Middle,
    /// `bottom`.
    Bottom,
}
