//! Kani harnesses for table layout. Compiled only under `cargo kani`.
//!
//! As in `flow/proofs.rs`, each harness checks **one step from any state**
//! satisfying its invariant (`state.rs`), with any input: no panic,
//! arithmetic overflow or out-of-bounds index is reachable, the step keeps
//! the invariant, and the properties its contract states hold. The start
//! states satisfy the invariants (asserted too), so by induction every state
//! the drivers reach on a table of **any size** does.
//!
//! Proved for every size (step harnesses): forming a table's steps
//! ([`start_row_any`], [`place_any`], [`end_row_any`], [`end_group_any`]),
//! a column's measures ([`widen_any`]) and a row's extent
//! ([`row_extent_any`]). For any input: the clamping of `colspan` and
//! `rowspan` ([`spans_any`]), a cell's outer measures
//! ([`cell_outer_any`]), §3.9.1's used width ([`used_width_any`]), the
//! table's intrinsic widths ([`table_intrinsic_any`]) and a cell's extra
//! padding ([`cell_offsets_any`]). Only on bounded values: a percentage
//! of a length ([`percent_of_small`]: up to 100% of up to 2^14 px).
//!
//! Removed at the 20 minute cap (CBMC's 64-bit division): `percent_of_any`
//! (unbounded inputs), and the running share's step, `share_step_any`
//! (any total, weights up to 2^31) and its shrunk `share_step_small`
//! (weights up to 2^12, totals up to 2^20), whose division is by a symbolic
//! divisor. The share is therefore **not proved by Kani**; `tests.rs`'s
//! `floors_match_wide_arithmetic` checks `floor_share` and `percent_of`
//! against 128-bit arithmetic natively, and `shares_add_up` the shares.
//!
//! Not covered, and why: the drivers, whose state is the box tree, the grid
//! and vectors of columns and rows (`grid.rs`'s `form`, `measure.rs`'s
//! `columns` and `span_contribution`, `distribute.rs`'s `auto_widths`,
//! `excess_shares` and `fixed_widths`, `rows.rs`'s `rows`, `fill` and
//! `tops`, and the walk's `enter_table`, `enter_cell` and `exit_table`).
//! Each is a fold of the steps above; the unit and golden tests run them.

use super::distribute::percent_of;
use super::grid::{end_group, end_row, place, spans, start_row};
use super::measure::{Sizes, cell_outer, table_intrinsic, used_width, widen};
use super::rows::{add_baseline, add_other, cell_offsets, row_height};
use super::state::{
    CellAlign, Former, HUNDRED, MAX_COLSPAN, MAX_COLUMNS, MAX_ROWSPAN, Measure, RowExtent, Spans,
    TableWidthInput,
};

/// 2^22 px in 1/64 px: within it, no sum of four values saturates.
const BOUND: i32 = 1 << 28;

fn small(v: i32) -> bool {
    v > -BOUND && v < BOUND
}

/// `colspan` and `rowspan` after HTML's parsing and clamping, for any
/// parse result.
#[kani::proof]
fn spans_any() {
    let c: Option<i64> = kani::any();
    let r: Option<i64> = kani::any();
    let s = spans(c, r);
    assert!(s.colspan >= 1 && s.colspan <= MAX_COLSPAN);
    assert!(s.rowspan >= 1 && s.rowspan <= MAX_ROWSPAN);
    assert!(s.downward == (r == Some(0)));
    if let Some(v) = c
        && v > 0
        && v <= 1000
    {
        assert!(i64::from(s.colspan) == v);
    }
}

/// Any spans the parser can give.
fn any_spans() -> Spans {
    let s: Spans = kani::any();
    kani::assume(s.colspan >= 1 && s.colspan <= MAX_COLSPAN);
    kani::assume(s.rowspan >= 1 && s.rowspan <= MAX_ROWSPAN);
    s
}

/// Any state satisfying the invariant, with rows still to count.
fn any_former() -> Former {
    let f: Former = kani::any();
    kani::assume(f.invariant());
    kani::assume(f.yheight < u64::MAX - u64::from(MAX_ROWSPAN));
    f
}

/// "The algorithm for processing rows", its start: the invariant is kept,
/// the current row exists and `xcurrent` is 0.
#[kani::proof]
fn start_row_any() {
    assert!(Former::START.invariant());
    let f = any_former();
    let g = start_row(f);
    assert!(g.invariant());
    assert!(g.xcurrent == 0);
    assert!(g.ycurrent == f.ycurrent);
    assert!(g.ycurrent < g.yheight);
    assert!(g.xwidth == f.xwidth);
}

/// Placing a cell: the invariant is kept, the cell is inside the grid at
/// the free column (or the last one when the grid is full), and `xcurrent`
/// moves to its right edge.
#[kani::proof]
fn place_any() {
    let f = any_former();
    kani::assume(f.ycurrent < f.yheight);
    let free: u32 = kani::any();
    kani::assume(f.xcurrent <= free && free <= f.xwidth);
    let s = any_spans();
    let (p, g) = place(f, free, s);
    assert!(g.invariant());
    assert!(p.width >= 1 && p.width <= s.colspan);
    assert!(p.height == s.rowspan);
    assert!(u64::from(p.x) + u64::from(p.width) <= u64::from(g.xwidth));
    assert!(p.y == f.ycurrent);
    assert!(p.y + u64::from(p.height) <= g.yheight);
    assert!(g.xcurrent == p.x + p.width);
    assert!(g.ycurrent == f.ycurrent);
    if f.xwidth < MAX_COLUMNS {
        assert!(p.x == free);
    } else {
        assert!(p.x == free || (free == MAX_COLUMNS && p.x == MAX_COLUMNS - 1));
    }
    // A cell is cut only at the column bound.
    if u64::from(p.x) + u64::from(s.colspan) <= u64::from(MAX_COLUMNS) {
        assert!(p.width == s.colspan);
    }
}

/// The end of a row: `ycurrent` moves down one, within `yheight`.
#[kani::proof]
fn end_row_any() {
    let f = any_former();
    kani::assume(f.ycurrent < f.yheight);
    let g = end_row(f);
    assert!(g.invariant());
    assert!(g.ycurrent == f.ycurrent + 1);
    assert!(g.yheight == f.yheight && g.xwidth == f.xwidth);
}

/// Ending a row group: `ycurrent` reaches `yheight`.
#[kani::proof]
fn end_group_any() {
    let f = any_former();
    let g = end_group(f);
    assert!(g.invariant());
    assert!(g.ycurrent == g.yheight && g.yheight == f.yheight);
}

/// "The largest of": the invariant is kept, nothing decreases, each
/// measure is at least its contribution.
#[kani::proof]
fn widen_any() {
    let m: Measure = kani::any();
    kani::assume(m.invariant());
    assert!(Measure::default().invariant());
    let (min, max, pct): (i32, i32, i64) = (kani::any(), kani::any(), kani::any());
    let n = widen(m, min, max, pct);
    assert!(n.invariant());
    assert!(n.min >= m.min && n.max >= m.max && n.pct >= m.pct);
    assert!(n.min >= min && n.max >= max);
    if pct <= HUNDRED {
        assert!(n.pct >= pct);
    }
}

/// A cell's outer measures (§3.8.2): the invariant holds, and the
/// min-content width covers the offsets and the content's min-content
/// width.
#[kani::proof]
fn cell_outer_any() {
    let z: Sizes = kani::any();
    kani::assume(z.offsets >= 0 && z.min_width >= 0);
    kani::assume(z.width.is_none_or(|w| w >= 0) && z.max_width.is_none_or(|w| w >= 0));
    let content: (i32, i32) = kani::any();
    let (constrained, nowrap): (bool, bool) = (kani::any(), kani::any());
    let m = cell_outer(content, &z, constrained, nowrap);
    assert!(m.invariant());
    assert!(m.min >= z.offsets);
    if small(content.0) && small(z.offsets) {
        assert!(i64::from(m.min) >= i64::from(content.0) + i64::from(z.offsets));
    }
}

/// CSS Tables 3 §3.9.1, for any input: the used min-width or more, and
/// exactly the section's two cases.
#[kani::proof]
fn used_width_any() {
    let t: TableWidthInput = kani::any();
    let w = used_width(t);
    let used_min = t.min_width.max(t.capmin).max(t.gridmin);
    assert!(w >= used_min);
    match t.width {
        Some(v) => assert!(w == v.max(used_min)),
        None => assert!(w == t.gridmax.min(t.available).max(used_min)),
    }
}

/// A table's min-content width is at most its max-content width.
#[kani::proof]
fn table_intrinsic_any() {
    let t: TableWidthInput = kani::any();
    let (lo, hi) = table_intrinsic(t);
    assert!(lo <= hi);
    assert!(lo >= t.min_width.max(t.capmin).max(t.gridmin));
}

/// A row's extent, from any state: the invariant is kept, the height
/// covers each cell, and the row's height its `height` too.
#[kani::proof]
fn row_extent_any() {
    assert!(RowExtent::EMPTY.invariant());
    let r: RowExtent = kani::any();
    kani::assume(r.invariant());
    let (above, below, h, spec): (i32, i32, i32, i32) =
        (kani::any(), kani::any(), kani::any(), kani::any());
    let a = add_baseline(r, above, below);
    assert!(a.invariant());
    assert!(a.baseline && a.above >= above && a.below >= below && a.height >= r.height);
    let o = add_other(r, h);
    assert!(o.invariant());
    assert!(o.height >= h && o.height >= r.height && o.above == r.above);
    let height = row_height(r, spec);
    assert!(height >= spec && height >= r.height && height >= 0);
}

/// A cell's extra padding: never negative, and with the cell's height they
/// make the larger of the rows' height and the cell's.
#[kani::proof]
fn cell_offsets_any() {
    let align: CellAlign = kani::any();
    let (span, baseline, height, cell_baseline): (i32, i32, i32, i32) =
        (kani::any(), kani::any(), kani::any(), kani::any());
    let (top, bottom) = cell_offsets(align, span, baseline, height, cell_baseline);
    assert!(top >= 0 && bottom >= 0);
    if small(span) && small(height) && height >= 0 {
        let total = i64::from(span.max(height));
        assert!(i64::from(top) + i64::from(height) + i64::from(bottom) == total);
        if align == CellAlign::Top {
            assert!(top == 0);
        }
    }
}

/// A percentage of a length, for percentages up to 100% and lengths up to
/// 2^14 px (unbounded inputs ran past the 20 minute cap;
/// `floors_match_wide_arithmetic` checks `percent_of` natively against
/// 128-bit arithmetic on any input): within the length.
#[kani::proof]
fn percent_of_small() {
    let p: i64 = kani::any();
    let basis: i32 = kani::any();
    kani::assume((0..=HUNDRED).contains(&p) && (0..1 << 20).contains(&basis));
    let v = percent_of(p, basis);
    assert!(v >= 0 && v <= basis);
}
