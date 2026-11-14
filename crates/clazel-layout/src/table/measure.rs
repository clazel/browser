//! Table measures: each cell's outer min-content and max-content widths
//! and percentage contribution, each column's measures with spanning cells
//! by increasing span, the table's GRIDMIN and GRIDMAX, and its used width
//! (phase-5.md item 5.15).
//!
//! Sources: CSS Tables 3 (csswg-drafts `e13fe879`) §3.8.1
//! `#computing-undistributable-space`, §3.8.2 `#computing-cell-measures`,
//! §3.8.3 `#computing-column-measures`, §3.9.1
//! `#computing-the-table-width`, §3.9.3.1 (fixed mode's measures); CSS 2.1
//! §17.5.2.1; the Quirks Mode Standard (commit `5a06deb5`) §3.9.
//!
//! Modelling choices (with `mod.rs`'s):
//!
//! - **The "offsets-adjusted" `width`, `min-width` and `max-width`** of a
//!   cell are its computed ones (`box-sizing` is `content-box` for cells),
//!   and the "cell intrinsic offsets" its horizontal borders and padding,
//!   with percentage padding as zero (as 5.14's `intrinsic.rs` counts it).
//!   A percentage `width` or `min-width` counts as zero in the length
//!   formulas; `auto` likewise, and in `min('max-width', 'width')` the term
//!   is left out (`mod.rs`).
//! - **A cell's content sizes** are 5.14's min-content and max-content
//!   widths of its content (`intrinsic.rs`), with the Quirks Mode Standard's
//!   §3.8 applied there.
//! - **"Its corresponding table-column"**: every column box covering the
//!   column, and every column group box; each contributes as §3.8.3 says.
//! - **Intrinsic percentage widths** are millionths of a percent, and every
//!   share of one is exact ([`super::distribute::share`]).

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{ComputedStyle, Lp, MaxSize, Size};
use clazel_style::cascade::hints::{attribute, is_html};

use super::distribute::{Fixed, share, to_px};
use super::grid::Grid;
use super::state::{HUNDRED, Measure, TableWidthInput};
use crate::boxes::{BoxId, BoxTree};

/// A box's `width`, `min-width` and `max-width` as the formulas read them
/// (the module's modelling choices).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Sizes {
    /// The horizontal borders and padding (zero for columns).
    pub offsets: i32,
    /// `width` when it is a length.
    pub width: Option<i32>,
    /// `width` when it is a percentage.
    pub width_pct: Option<i64>,
    /// `min-width` when it is a length, else zero.
    pub min_width: i32,
    /// `max-width` when it is a length.
    pub max_width: Option<i32>,
    /// `max-width` when it is a percentage.
    pub max_pct: Option<i64>,
}

/// The [`Sizes`] of style `s`, with intrinsic offsets `offsets`.
pub fn sizes_of(s: &ComputedStyle, offsets: i32) -> Sizes {
    let (width, width_pct) = match s.width {
        Size::Lp(Lp::Px64(w)) => (Some(w.max(0)), None),
        Size::Lp(Lp::Percent(p)) => (None, Some(p.millionths)),
        Size::Auto => (None, None),
    };
    let min_width = match s.min_width {
        Size::Lp(Lp::Px64(w)) => w.max(0),
        _ => 0,
    };
    let (max_width, max_pct) = match s.max_width {
        MaxSize::Lp(Lp::Px64(w)) => (Some(w.max(0)), None),
        MaxSize::Lp(Lp::Percent(p)) => (None, Some(p.millionths)),
        MaxSize::None => (None, None),
    };
    Sizes {
        offsets: offsets.max(0),
        width,
        width_pct,
        min_width,
        max_width,
        max_pct,
    }
}

/// The cell intrinsic offsets of a cell of style `s` (§3.8.2: "In
/// separated-borders mode: the computed horizontal padding and border of
/// the table-cell"), with percentage padding as zero.
pub fn cell_offsets(s: &ComputedStyle) -> i32 {
    let fixed = |v: Lp| match v {
        Lp::Px64(x) => x.max(0),
        Lp::Percent(_) => 0,
    };
    let [_, br, _, bl] = s.border_width;
    let [_, pr, _, pl] = s.padding;
    [br.max(0), bl.max(0), fixed(pr), fixed(pl)]
        .iter()
        .fold(0i32, |a, &x| a.saturating_add(x))
}

/// §3.8.2's percentage contribution: "min(percentage 'width', percentage
/// 'max-width'). If the computed values are not percentages, then 0% is
/// used for 'width', and an infinite percentage is used for 'max-width'."
fn percentage(z: &Sizes) -> i64 {
    let w = z.width_pct.unwrap_or(0);
    let m = z.max_pct.unwrap_or(i64::MAX);
    w.min(m).clamp(0, HUNDRED)
}

/// §3.8.2's outer min-content and max-content widths and percentage
/// contribution of a cell whose content has min-content and max-content
/// widths `content` (`state.rs`'s contract). `constrained` selects the
/// formula for "a constrained column"; `nowrap` is the Quirks Mode
/// Standard's §3.9 (the cell's `width` as a minimum).
pub fn cell_outer(content: (i32, i32), z: &Sizes, constrained: bool, nowrap: bool) -> Measure {
    let (cmin, cmax) = (content.0.max(0), content.1.max(0));
    let width = z.width.unwrap_or(0);
    // "The outer min-content width of a table-cell is max('min-width',
    // min-content width) adjusted by the cell intrinsic offsets."
    let mut min = z.min_width.max(cmin);
    // §3.9: "an outer min-content width of a table cell … that is the bigger
    // value of cell's computed value of the 'width' property and the outer
    // min-content width of a table cell".
    if nowrap {
        min = min.max(width);
    }
    let max = if constrained {
        // "max('min-width', 'width', min-content width, min('max-width',
        // 'width'))": the last term is at most 'width'.
        z.min_width.max(width).max(cmin)
    } else {
        // "max('min-width', 'width', min-content width, min('max-width',
        // max-content width))".
        let capped = z.max_width.map_or(cmax, |m| m.min(cmax));
        z.min_width.max(width).max(cmin).max(capped)
    };
    let max = if nowrap { max.max(min) } else { max };
    Measure {
        min: min.saturating_add(z.offsets),
        max: max.max(min).saturating_add(z.offsets),
        pct: percentage(z),
    }
}

/// §3.8.2's outer widths of a column or column group box: "max('min-width',
/// 'width')" and "max('min-width', min('max-width', 'width'))", with its
/// percentage contribution.
pub fn track_outer(z: &Sizes) -> Measure {
    let min = z.min_width.max(z.width.unwrap_or(0));
    let max = match z.width {
        Some(w) => z.min_width.max(z.max_width.map_or(w, |m| m.min(w))),
        None => z.min_width,
    };
    Measure {
        min,
        max,
        pct: percentage(z),
    }
}

/// "The largest of" each of `m`'s measures and a contribution, with the
/// max-content width kept at least the min-content width (`state.rs`'s
/// contract).
pub fn widen(m: Measure, min: i32, max: i32, pct: i64) -> Measure {
    let min = m.min.max(min).max(0);
    let max = m.max.max(max).max(min);
    Measure {
        min,
        max,
        pct: m.pct.max(pct).clamp(0, HUNDRED),
    }
}

/// One column of a table, as §3.9.3 reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Column {
    /// Its measures.
    pub measure: Measure,
    /// §3.8.3: "A column is constrained if its corresponding
    /// table-column-group (if any), its corresponding table-column (if
    /// any), or any of the cells spanning only that column has a computed
    /// 'width' that is not 'auto', and is not a percentage."
    pub constrained: bool,
    /// A cell starts in it.
    pub originating: bool,
}

/// What the measures read about a table: its tree and document, every
/// box's style, every box's content sizes (5.14's `intrinsic.rs`), and
/// the document's mode.
pub struct Inputs<'a> {
    /// The box tree.
    pub tree: &'a BoxTree,
    /// The document (for `nowrap`).
    pub arena: &'a Arena,
    /// Every box's style.
    pub styles: &'a [ComputedStyle],
    /// Every box's content `(min-content, max-content)` widths.
    pub content: &'a [(i32, i32)],
    /// Quirks mode.
    pub quirks: bool,
}

impl Inputs<'_> {
    fn style(&self, b: BoxId) -> Option<&ComputedStyle> {
        self.styles.get(b)
    }

    fn sizes(&self, b: BoxId, offsets: bool) -> Sizes {
        self.style(b).map_or(Sizes::default(), |s| {
            sizes_of(s, if offsets { cell_offsets(s) } else { 0 })
        })
    }

    /// The Quirks Mode Standard's §3.9: "cell is a td element or a th
    /// element", "cell has a nowrap attribute", "The computed value of the
    /// 'width' property of cell is a <length> that is not zero."
    fn nowrap(&self, b: BoxId) -> bool {
        if !self.quirks {
            return false;
        }
        let Some(node) = self.tree.get(b).and_then(|x| x.node) else {
            return false;
        };
        if node >= self.arena.len()
            || !(is_html(self.arena, node, "td") || is_html(self.arena, node, "th"))
        {
            return false;
        }
        let has = match self.arena.kind(node) {
            ExecKind::Element { attributes, .. } => attribute(attributes, "nowrap").is_some(),
            _ => false,
        };
        has && self
            .style(b)
            .is_some_and(|s| matches!(s.width, Size::Lp(Lp::Px64(w)) if w != 0))
    }
}

/// The column measures of `grid` (§3.8.3), with horizontal border spacing
/// `spacing`.
pub fn columns(grid: &Grid, x: &Inputs<'_>, spacing: i32) -> Vec<Column> {
    let n = grid.columns;
    let mut cols = vec![Column::default(); n];
    // "the width specified for the column: the outer min-content width of
    // its corresponding table-column, if any (and not auto); the outer
    // min-content width of its corresponding table-column-group, if any";
    // likewise the max-content widths and percentage contributions.
    for t in grid.column_boxes.iter().chain(grid.column_groups.iter()) {
        let z = x.sizes(t.owner, false);
        let m = track_outer(&z);
        for c in cols.iter_mut().skip(t.start).take(t.span) {
            c.measure = widen(c.measure, m.min, m.max, m.pct);
            c.constrained |= z.width.is_some();
        }
    }
    // "or any of the cells spanning only that column".
    for s in &grid.cells {
        if s.cols == 1
            && x.sizes(s.cell, true).width.is_some()
            && let Some(c) = cols.get_mut(s.col)
        {
            c.constrained = true;
        }
    }
    for s in &grid.cells {
        if let Some(c) = cols.get_mut(s.col) {
            c.originating = true;
        }
    }
    // "min-content width of a column based on cells of span up to 1" and
    // the max-content width and intrinsic percentage width likewise.
    for s in grid.cells.iter().filter(|s| s.cols == 1) {
        let Some(constrained) = cols.get(s.col).map(|c| c.constrained) else {
            continue;
        };
        let content = x.content.get(s.cell).copied().unwrap_or((0, 0));
        let m = cell_outer(
            content,
            &x.sizes(s.cell, true),
            constrained,
            x.nowrap(s.cell),
        );
        if let Some(c) = cols.get_mut(s.col) {
            c.measure = widen(c.measure, m.min, m.max, m.pct);
        }
    }
    // "the column's non-spanning max-content width".
    let nonspanning: Vec<i64> = cols.iter().map(|c| i64::from(c.measure.max)).collect();
    // Spans N = 2, 3, …: each from the measures "based on cells of span up
    // to N-1", so a span's contributions are all found before any applies.
    let mut spanning: Vec<_> = grid.cells.iter().filter(|s| s.cols > 1).collect();
    spanning.sort_by_key(|s| s.cols);
    let mut i = 0usize;
    while let Some(first) = spanning.get(i) {
        let span = first.cols;
        let mut contributions: Vec<(usize, Measure)> = Vec::new();
        while let Some(s) = spanning.get(i).filter(|s| s.cols == span) {
            i = i.saturating_add(1);
            let z = x.sizes(s.cell, true);
            let content = x.content.get(s.cell).copied().unwrap_or((0, 0));
            let cell = cell_outer(content, &z, z.width.is_some(), x.nowrap(s.cell));
            let range = s.col..s.col.saturating_add(s.cols).min(n);
            let Some(prev) = cols.get(range.clone()) else {
                continue;
            };
            let nonspan = nonspanning.get(range.clone()).unwrap_or(&[]);
            for (k, m) in span_contribution(prev, nonspan, &cell, spacing)
                .into_iter()
                .enumerate()
            {
                contributions.push((range.start.saturating_add(k), m));
            }
        }
        for (k, m) in contributions {
            if let Some(c) = cols.get_mut(k) {
                c.measure = widen(c.measure, m.min, m.max, m.pct);
            }
        }
    }
    // "intrinsic percentage width of a column: the smaller of: the intrinsic
    // percentage width of the column based on cells of span up to N … 100%
    // minus the sum of the intrinsic percentage width of all prior columns".
    let mut prior = 0i64;
    for c in &mut cols {
        let p = c.measure.pct.min(HUNDRED.saturating_sub(prior)).max(0);
        c.measure.pct = p;
        prior = prior.saturating_add(p);
    }
    cols
}

/// §3.8.3's contributions of a cell spanning columns `prev` (their measures
/// based on cells of smaller spans; `nonspan` their non-spanning
/// max-content widths), with outer measures `cell`.
pub fn span_contribution(
    prev: &[Column],
    nonspan: &[i64],
    cell: &Measure,
    spacing: i32,
) -> Vec<Measure> {
    let n = prev.len();
    let sum = |f: &dyn Fn(&Column) -> i64| prev.iter().fold(0i64, |a, c| a.saturating_add(f(c)));
    // "Define the baseline min-content width as the sum of the min-content
    // widths … Define the baseline max-content width as the sum of the
    // max-content widths … Define the baseline border spacing as the sum of
    // the horizontal border-spacing for any columns spanned by the cell,
    // other than the one in which the cell originates."
    let bmin = sum(&|c| i64::from(c.measure.min));
    let bmax = sum(&|c| i64::from(c.measure.max));
    let bsp =
        i64::from(spacing.max(0)).saturating_mul(i64::try_from(n.saturating_sub(1)).unwrap_or(0));
    let cmin = i64::from(cell.min);
    let cmax = i64::from(cell.max);
    // The min-content contribution's first product: "the ratio of: the
    // max-content width … minus the min-content width …, to the baseline
    // max-content width minus the baseline min-content width or zero if
    // this ratio is undefined, and the outer min-content width of the cell
    // minus the baseline min-content width and the baseline border spacing,
    // clamped to be at least 0 and at most the difference between the
    // baseline max-content width and the baseline min-content width".
    let room = bmax.saturating_sub(bmin).max(0);
    let first = cmin.saturating_sub(bmin).saturating_sub(bsp).clamp(0, room);
    let gaps: Vec<i64> = prev
        .iter()
        .map(|c| {
            i64::from(c.measure.max)
                .saturating_sub(i64::from(c.measure.min))
                .max(0)
        })
        .collect();
    let t1 = if room == 0 {
        vec![0; n]
    } else {
        share(first, &gaps)
    };
    // The second product: "the ratio of the max-content width … of the
    // column to the baseline max-content width" and "the outer min-content
    // width of the cell minus the baseline max-content width and baseline
    // border spacing, or 0 if this is negative". When the baseline
    // max-content width is zero the ratio is undefined; the excess is shared
    // equally (`docs/ERRATA.md`).
    let maxes: Vec<i64> = prev.iter().map(|c| i64::from(c.measure.max)).collect();
    let t2 = share(cmin.saturating_sub(bmax).saturating_sub(bsp).max(0), &maxes);
    // The max-content contribution: "the max-content width … of the column"
    // plus "the ratio of the max-content width … to the baseline max-content
    // width" times "the outer max-content width of the cell minus the
    // baseline max-content width and the baseline border spacing, or 0 if
    // this is negative".
    let t3 = share(cmax.saturating_sub(bmax).saturating_sub(bsp).max(0), &maxes);
    // The percentage contribution, for columns whose percentage so far is
    // 0%: "Start with the percentage contribution of the cell. Subtract the
    // intrinsic percentage width … of all columns that the cell spans. If
    // this gives a negative result, change it to 0%. Multiply by the ratio
    // of the column's non-spanning max-content width to the sum of the
    // non-spanning max-content widths of all columns spanned by the cell
    // that have an intrinsic percentage width … equal to 0%. However, if
    // this ratio is undefined because the denominator is zero, instead use
    // the 1 divided by the number of columns spanned by the cell that have
    // an intrinsic percentage width … equal to zero."
    let spent = sum(&|c| c.measure.pct);
    let left = cell.pct.saturating_sub(spent).max(0);
    let zero: Vec<bool> = prev.iter().map(|c| c.measure.pct == 0).collect();
    let weights: Vec<i64> = zero
        .iter()
        .zip(nonspan.iter().chain(std::iter::repeat(&0)))
        .map(|(&z, &w)| if z { w.max(0) } else { 0 })
        .collect();
    let weights = if weights.iter().any(|&w| w > 0) {
        weights
    } else {
        zero.iter().map(|&z| i64::from(z)).collect()
    };
    let t4 = if zero.iter().any(|&z| z) {
        share(left, &weights)
    } else {
        vec![0; n]
    };
    prev.iter()
        .enumerate()
        .map(|(k, c)| {
            let get = |v: &[i64]| v.get(k).copied().unwrap_or(0);
            let min = i64::from(c.measure.min)
                .saturating_add(get(&t1))
                .saturating_add(get(&t2));
            let max = i64::from(c.measure.max).saturating_add(get(&t3));
            // "If the intrinsic percentage width of a column based on cells
            // of span up to N-1 is greater than 0%, then [it] is the same".
            let pct = if c.measure.pct > 0 { 0 } else { get(&t4) };
            Measure {
                min: to_px(min),
                max: to_px(max),
                pct,
            }
        })
        .collect()
}

/// The total horizontal border spacing of `columns` columns (§3.8.2: "the
/// horizontal component of the computed value of the border-spacing
/// property times one plus the number of columns in the table", or 0 with
/// no column).
pub fn total_spacing(columns: usize, spacing: i32) -> i32 {
    if columns == 0 {
        return 0;
    }
    let n = i64::try_from(columns).unwrap_or(i64::MAX).saturating_add(1);
    to_px(i64::from(spacing.max(0)).saturating_mul(n))
}

/// The sum of the columns' min-content and max-content widths with the
/// total border spacing: GRIDMIN and GRIDMAX less the table's borders and
/// padding (`mod.rs`).
pub fn grid_sizes(cols: &[Column], spacing: i32) -> (i32, i32) {
    let sp = i64::from(total_spacing(cols.len(), spacing));
    let (lo, hi) = cols.iter().fold((sp, sp), |(a, b), c| {
        (
            a.saturating_add(i64::from(c.measure.min)),
            b.saturating_add(i64::from(c.measure.max)),
        )
    });
    (to_px(lo), to_px(hi))
}

/// CSS 2.1 §17.5.2.1's column widths before distribution: "A column element
/// with a value other than 'auto' for the 'width' property sets the width
/// for that column. Otherwise, a cell in the first row with a value other
/// than 'auto' for the 'width' property determines the width for that
/// column. If the cell spans more than one column, the width is divided
/// over the columns." A first-row cell's length is its outer width; its
/// percentage ignores its borders and padding (§3.9.3.1).
pub fn fixed_columns(grid: &Grid, x: &Inputs<'_>, spacing: i32) -> Vec<Fixed> {
    let mut out = vec![Fixed::Auto; grid.columns];
    for t in &grid.column_boxes {
        let z = x.sizes(t.owner, false);
        let f = match (z.width, z.width_pct) {
            (Some(w), _) => Fixed::Length(w),
            (None, Some(p)) => Fixed::Percent(p.max(0)),
            _ => continue,
        };
        for c in out.iter_mut().skip(t.start).take(t.span) {
            *c = f;
        }
    }
    for s in grid.cells.iter().filter(|s| s.row == 0) {
        let z = x.sizes(s.cell, true);
        let range = s.col..s.col.saturating_add(s.cols).min(grid.columns);
        let Some(cols) = out.get(range.clone()) else {
            continue;
        };
        let open: Vec<i64> = cols
            .iter()
            .map(|c| i64::from(matches!(c, Fixed::Auto)))
            .collect();
        if !open.iter().any(|&o| o > 0) {
            continue;
        }
        let set: Vec<Fixed> = match (z.width, z.width_pct) {
            (Some(w), _) => {
                let gaps = i64::from(spacing.max(0))
                    .saturating_mul(i64::try_from(s.cols.saturating_sub(1)).unwrap_or(0));
                let taken = cols.iter().fold(0i64, |a, c| match c {
                    Fixed::Length(v) => a.saturating_add(i64::from(*v)),
                    _ => a,
                });
                let total = i64::from(w.saturating_add(z.offsets))
                    .saturating_sub(gaps)
                    .saturating_sub(taken)
                    .max(0);
                share(total, &open)
                    .into_iter()
                    .map(|v| Fixed::Length(to_px(v)))
                    .collect()
            }
            (None, Some(p)) => share(p.max(0), &open)
                .into_iter()
                .map(Fixed::Percent)
                .collect(),
            _ => continue,
        };
        for ((c, o), v) in out
            .get_mut(range)
            .unwrap_or(&mut [])
            .iter_mut()
            .zip(open)
            .zip(set)
        {
            if o > 0 {
                *c = v;
            }
        }
    }
    out
}

/// The sum of the lengths fixed layout gives columns `given`, with the
/// total border spacing: GRIDMIN in fixed mode (§3.9.3.1: "The min-content
/// width of percent-columns and auto-columns is considered to be zero"),
/// less the table's borders and padding.
pub fn fixed_sizes(given: &[Fixed], spacing: i32) -> i32 {
    let sp = i64::from(total_spacing(given.len(), spacing));
    to_px(given.iter().fold(sp, |a, g| match g {
        Fixed::Length(w) => a.saturating_add(i64::from((*w).max(0))),
        _ => a,
    }))
}

/// CSS Tables 3 §3.9.1: the used width of a table (`state.rs`'s contract).
pub fn used_width(t: TableWidthInput) -> i32 {
    // "The used min-width of a table is the greater of the resolved
    // 'min-width', CAPMIN, and GRIDMIN."
    let used_min = t.min_width.max(t.capmin).max(t.gridmin);
    match t.width {
        // "If the table-root's 'width' property has a computed value
        // (resolving to resolved-table-width) other than auto, the used
        // width is the greater of resolved-table-width, and the used
        // min-width of the table."
        Some(w) => w.max(used_min),
        // "If the table-root has 'width: auto', the used width is the
        // greater of min(GRIDMAX, the table's containing block width), the
        // used min-width of the table."
        None => t.gridmax.min(t.available).max(used_min),
    }
}

/// A table's min-content and max-content widths as its wrapper box
/// contributes them (its border box): §3.9.1's used width with no room
/// (min-content) and with unlimited room (max-content); a percentage
/// `width` counts as `auto`.
pub fn table_intrinsic(t: TableWidthInput) -> (i32, i32) {
    let lo = used_width(TableWidthInput { available: 0, ..t });
    let hi = used_width(TableWidthInput {
        available: i32::MAX,
        ..t
    });
    (lo, hi.max(lo))
}
