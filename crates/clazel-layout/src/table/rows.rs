//! Row heights and the vertical alignment of cells (phase-5.md item 5.15).
//!
//! Sources: CSS 2.1 §17.5.3 "Table height algorithms"; CSS Tables 3
//! (csswg-drafts `e13fe879`) §3.10.1 `#computing-the-table-height`, §3.10.2
//! `#row-layout`, §3.10.5 `#height-distribution-algorithm`, §3.11
//! `#bounding-box-assignment`.
//!
//! Modelling choices: `mod.rs`'s "Row heights", "The table's `height`",
//! "`vertical-align`" and "Baselines".

use super::distribute::{share, to_px};
use super::grid::Grid;
use super::state::{CellAlign, RowExtent};
use crate::flow::length::half_down;

/// A cell aligned on its baseline: `above` from its top to its baseline,
/// `below` the rest of its height (`state.rs`'s contract).
pub fn add_baseline(r: RowExtent, above: i32, below: i32) -> RowExtent {
    let above = r.above.max(above.max(0));
    let below = r.below.max(below.max(0));
    RowExtent {
        above,
        below,
        // "The row now has a top, possibly a baseline, and a provisional
        // height, which is the distance from the top to the lowest bottom
        // of the cells positioned so far."
        height: r.height.max(above.saturating_add(below)),
        baseline: true,
    }
}

/// A cell aligned at the top, middle or bottom, of height `height`: "If
/// any of the remaining cells, those aligned at the bottom or the middle,
/// have a height that is larger than the current height of the row, the
/// height of the row will be increased to the maximum of those cells, by
/// lowering the bottom" (a top cell's bottom is likewise the row's lowest).
pub fn add_other(r: RowExtent, height: i32) -> RowExtent {
    RowExtent {
        height: r.height.max(height.max(0)),
        ..r
    }
}

/// The row's height: "the maximum of the row's computed 'height', the
/// computed 'height' of each cell in the row, and the minimum height (MIN)
/// required by the cells" (CSS 2.1 §17.5.3), `specified` the largest of the
/// first two.
pub fn row_height(r: RowExtent, specified: i32) -> i32 {
    r.height.max(specified.max(0))
}

/// The extra top and bottom padding of a cell of height `height` and
/// baseline `cell_baseline` (from its top) in rows `span` high whose first
/// row's baseline is `baseline` (from that row's top), aligned by `align`
/// (`state.rs`'s contract).
pub fn cell_offsets(
    align: CellAlign,
    span: i32,
    baseline: i32,
    height: i32,
    cell_baseline: i32,
) -> (i32, i32) {
    let height = height.max(0);
    let free = span.max(height).saturating_sub(height).max(0);
    let top = match align {
        // "The top of the cell box is aligned with the top of the first row
        // it spans."
        CellAlign::Top => 0,
        // "The bottom of the cell box is aligned with the bottom of the
        // last row it spans."
        CellAlign::Bottom => free,
        // "The center of the cell is aligned with the center of the rows it
        // spans."
        CellAlign::Middle => half_down(free),
        // "The baseline of the cell is put at the same height as the
        // baseline of the first of the rows it spans."
        CellAlign::Baseline => baseline.saturating_sub(cell_baseline).clamp(0, free),
    };
    (top, free.saturating_sub(top))
}

/// What a row's layout reads about one cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CellRow {
    /// Its border box height as its content made it.
    pub height: i32,
    /// Its baseline, from its border box top (CSS 2.1 §17.5.3).
    pub baseline: i32,
    /// Its alignment.
    pub align: CellAlign,
    /// Its `height` as a minimum for its rows (border box; 0 for `auto` or
    /// a percentage).
    pub specified: i32,
}

/// Each row's height and baseline (from its top; `None` with no cell
/// aligned on its baseline).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rows {
    /// The heights.
    pub heights: Vec<i32>,
    /// The baselines.
    pub baselines: Vec<Option<i32>>,
    /// Whether each row is an "auto-height" row (§3.10.5: "a row whose
    /// size is only determined by its content size and none of the
    /// specified heights").
    pub auto: Vec<bool>,
}

/// The rows of `grid`: `cells[i]` for `grid.cells[i]`, `specified[r]` row
/// `r`'s own `height` (a length, else 0), with vertical border spacing
/// `spacing` (CSS 2.1 §17.5.3; CSS Tables 3 §3.10.2).
pub fn rows(grid: &Grid, cells: &[CellRow], specified: &[i32], spacing: i32) -> Rows {
    let n = grid.rows;
    let mut ext = vec![RowExtent::EMPTY; n];
    let mut spec: Vec<i32> = (0..n)
        .map(|r| specified.get(r).copied().unwrap_or(0).max(0))
        .collect();
    let mut auto: Vec<bool> = spec.iter().map(|&s| s == 0).collect();
    // "In this hypothetical linebox, cell heights are considered auto …
    // cells spanning multiple rows are considered having a height of 0px
    // (but their correct baseline)."
    for (slot, c) in grid.cells.iter().zip(cells) {
        let Some(e) = ext.get_mut(slot.row) else {
            continue;
        };
        let single = slot.rows == 1;
        let h = if single { c.height } else { 0 };
        *e = match c.align {
            CellAlign::Baseline => add_baseline(*e, c.baseline, h.saturating_sub(c.baseline)),
            _ => add_other(*e, h),
        };
        // "the computed 'height' of each cell spanning the current row
        // exclusively".
        if single && c.specified > 0 {
            if let Some(s) = spec.get_mut(slot.row) {
                *s = (*s).max(c.specified);
            }
            if let Some(a) = auto.get_mut(slot.row) {
                *a = false;
            }
        }
    }
    let mut heights: Vec<i32> = ext
        .iter()
        .zip(&spec)
        .map(|(e, &s)| row_height(*e, s))
        .collect();
    // Cells spanning rows, by increasing span: "the sum of the row heights
    // involved must be great enough to encompass the cell spanning the
    // rows", any height lacking shared in proportion to the rows' heights.
    let mut spanning: Vec<(usize, &CellRow)> = grid
        .cells
        .iter()
        .zip(cells)
        .enumerate()
        .filter(|(_, (s, _))| s.rows > 1)
        .map(|(i, (_, c))| (i, c))
        .collect();
    spanning.sort_by_key(|&(i, _)| grid.cells.get(i).map_or(0, |s| s.rows));
    for (i, c) in spanning {
        let Some(slot) = grid.cells.get(i) else {
            continue;
        };
        let range = slot.row..slot.row.saturating_add(slot.rows).min(n);
        let Some(hs) = heights.get(range.clone()) else {
            continue;
        };
        let gaps = i64::from(spacing.max(0))
            .saturating_mul(i64::try_from(hs.len().saturating_sub(1)).unwrap_or(0));
        let have = hs.iter().fold(gaps, |a, &h| a.saturating_add(i64::from(h)));
        let need = i64::from(c.height.max(c.specified)).saturating_sub(have);
        if need <= 0 {
            continue;
        }
        let weights: Vec<i64> = hs.iter().map(|&h| i64::from(h)).collect();
        let extra = share(need, &weights);
        if let Some(hs) = heights.get_mut(range) {
            for (h, e) in hs.iter_mut().zip(extra) {
                *h = h.saturating_add(to_px(e));
            }
        }
    }
    let baselines = ext.iter().map(|e| e.baseline.then_some(e.above)).collect();
    Rows {
        heights,
        baselines,
        auto,
    }
}

/// CSS Tables 3 §3.10.5 with no second pass: rows `heights` grown to fill
/// `target` when they are shorter; "if the table owns any “auto-height”
/// row …, each non-auto-height row receives its reference height and
/// auto-height rows receive their reference size plus some increment which
/// is equal to the height missing to amount to the specified table height
/// divided by the amount of such rows. Else, all rows receive their
/// reference size plus some increment which is equal to the height missing
/// … divided by the amount of rows."
pub fn fill(heights: &mut [i32], auto: &[bool], target: i64) {
    let have = heights
        .iter()
        .fold(0i64, |a, &h| a.saturating_add(i64::from(h)));
    let missing = target.saturating_sub(have);
    if missing <= 0 || heights.is_empty() {
        return;
    }
    let any_auto = auto.iter().take(heights.len()).any(|&a| a);
    let weights: Vec<i64> = (0..heights.len())
        .map(|r| i64::from(!any_auto || auto.get(r).copied().unwrap_or(false)))
        .collect();
    for (h, e) in heights.iter_mut().zip(share(missing, &weights)) {
        *h = h.saturating_add(to_px(e));
    }
}

/// The tops of `heights` rows with vertical border spacing `spacing`, in
/// the table's content box (§3.11: "the vertical 'border-spacing' times the
/// amount of previous visible … rows plus one"), and the grid's content
/// height (the rows and spacing; zero with no row).
pub fn tops(heights: &[i32], spacing: i32) -> (Vec<i32>, i32) {
    let sp = spacing.max(0);
    let mut y = sp;
    let mut out = Vec::with_capacity(heights.len());
    for &h in heights {
        out.push(y);
        y = y.saturating_add(h).saturating_add(sp);
    }
    (out, if heights.is_empty() { 0 } else { y })
}
