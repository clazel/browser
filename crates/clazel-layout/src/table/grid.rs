//! The grid of a table box: HTML's "forming a table" over the box tree
//! (CSS Tables 3 §3.3.1), then §3.3.2's track merging (phase-5.md item
//! 5.15).
//!
//! Sources: HTML (commit `4c54fae1`) §4.9.12.1 "Forming a table", "the
//! algorithm for processing row groups", "the algorithm for ending a row
//! group", "the algorithm for processing rows" and "the algorithm for
//! growing downward-growing cells"; CSS Tables 3 (csswg-drafts `e13fe879`)
//! §3.3.1 `#dimensioning-the-row-column-grid--step1`, §3.3.2
//! `#dimensioning-the-row-column-grid--step2`; CSS 2.1 §17.2 (header and
//! footer groups).
//!
//! Modelling choices (with `mod.rs`'s):
//!
//! - **Elements are boxes.** "The table element" is the table box; its
//!   "children" are its child boxes, which item 5.13's §17.2.1 fixup has
//!   made proper table children (captions are in the wrapper box, and are
//!   associated by it, not here). A `colgroup` is a column group box, a
//!   `col` a column box, a `thead`, `tbody` or `tfoot` a row group box (by
//!   its display type), a `tr` a row box and a `td` or `th` a cell box.
//!   Attributes are read only from an HTML element of the same type (§3.3.1).
//! - **The order of the children** is CSS 2.1 §17.2's: the first header
//!   group first, the first footer group last (`mod.rs`). HTML's own
//!   handling of `tfoot` ("add that element to the list of pending tfoot
//!   elements") is that move for the one footer CSS keeps.
//! - **The "Cells" loop** ("While xcurrent is less than xwidth and the slot
//!   with coordinate (xcurrent, ycurrent) already has a cell assigned to it,
//!   increase xcurrent by 1") reads a record of covered slots: for each
//!   column, the row a cell covering it reaches and that cell's right edge,
//!   so the loop jumps over a cell at a time. A slot is covered when a cell
//!   placed in an earlier step covers it; cells are placed row by row, so
//!   the record's latest row per column is exact.
//! - **Downward-growing cells** (`rowspan=0`) cover every later row until
//!   their group ends, when they are given the group's last row.
//! - **"Ending a row group"** runs its loop's increments in one step
//!   (`end_group`); the cells it grows reach `yheight`, as the loop makes
//!   them.
//! - **Track merging** (§3.3.2): a column `x` (`x > 0`) is merged into the
//!   one before it when no cell starts or ends at `x` (then "both the said
//!   track and the previous one are spanned by the exact same set of
//!   cells") and no column box or column group box defines it; rows
//!   likewise with row boxes. A merged track keeps its first HTML track's
//!   place. In fixed layout no column is merged.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::hints::{attribute, is_html};
use clazel_style::cascade::legacy::non_negative_integer;

use super::state::{Former, MAX_COLSPAN, MAX_COLUMNS, MAX_ROWSPAN, Placed, Spans};
use crate::boxes::{BoxId, BoxKind, BoxTree, Class, RowGroup};

/// HTML §4.9.12.1's parsing and clamping of a cell's `colspan` and
/// `rowspan`, each the result of the rules for parsing non-negative
/// integers (`None` for an absent attribute or an error).
pub fn spans(colspan: Option<i64>, rowspan: Option<i64>) -> Spans {
    // "If the current cell has a colspan attribute, then parse that
    // attribute's value, and let colspan be the result. If parsing that
    // value failed, or returned zero, or if the attribute is absent, then
    // let colspan be 1, instead. If colspan is greater than 1000, let it be
    // 1000 instead."
    let c = match colspan {
        Some(v) if v > 0 => v.min(i64::from(MAX_COLSPAN)),
        _ => 1,
    };
    // "If the current cell has a rowspan attribute, then parse that
    // attribute's value, and let rowspan be the result. If parsing that
    // value failed or if the attribute is absent, then let rowspan be 1,
    // instead. If rowspan is greater than 65534, let it be 65534 instead."
    // (The rules never return a negative number; one is a failure here.)
    let r = match rowspan {
        Some(v) if v >= 0 => v.min(i64::from(MAX_ROWSPAN)),
        _ => 1,
    };
    // "Let cell grows downward be false. If rowspan is zero, then set cell
    // grows downward to true and set rowspan to 1."
    let downward = r == 0;
    Spans {
        colspan: u32::try_from(c).unwrap_or(1),
        rowspan: if downward {
            1
        } else {
            u32::try_from(r).unwrap_or(1)
        },
        downward,
    }
}

/// "The algorithm for processing rows", its first steps.
pub fn start_row(f: Former) -> Former {
    let mut f = f;
    // 1. "If yheight is equal to ycurrent, then increase yheight by 1.
    // (ycurrent is never greater than yheight.)"
    if f.yheight == f.ycurrent {
        f.yheight = f.yheight.saturating_add(1);
    }
    // 2. "Let xcurrent be 0."
    f.xcurrent = 0;
    f
}

/// "The algorithm for processing rows", from "If xcurrent is equal to
/// xwidth" to "Increase xcurrent by colspan", for a cell whose first free
/// column is `free` (`state.rs`'s contract).
pub fn place(f: Former, free: u32, s: Spans) -> (Placed, Former) {
    let mut f = f;
    let mut x = free.max(f.xcurrent).min(f.xwidth);
    // "If xcurrent is equal to xwidth, increase xwidth by 1. (xcurrent is
    // never greater than xwidth.)" At the column bound the cell goes in the
    // last column instead (`mod.rs`, hostile input).
    if x == f.xwidth {
        if f.xwidth < MAX_COLUMNS {
            f.xwidth = f.xwidth.saturating_add(1);
        } else {
            x = MAX_COLUMNS.saturating_sub(1);
        }
    }
    // The cell is cut at the column bound.
    let width = s.colspan.max(1).min(MAX_COLUMNS.saturating_sub(x)).max(1);
    let right = x.saturating_add(width);
    // "If xwidth < xcurrent+colspan, then let xwidth be xcurrent+colspan."
    if f.xwidth < right {
        f.xwidth = right;
    }
    // "If yheight < ycurrent+rowspan, then let yheight be ycurrent+rowspan."
    let height = s.rowspan.max(1);
    let bottom = f.ycurrent.saturating_add(u64::from(height));
    if f.yheight < bottom {
        f.yheight = bottom;
    }
    // "Let the slots with coordinates (x, y) such that xcurrent ≤ x <
    // xcurrent+colspan and ycurrent ≤ y < ycurrent+rowspan be covered by a
    // new cell c, anchored at (xcurrent, ycurrent), which has width colspan
    // and height rowspan".
    let placed = Placed {
        x,
        y: f.ycurrent,
        width,
        height,
    };
    // "Increase xcurrent by colspan."
    f.xcurrent = right;
    (placed, f)
}

/// "Increase ycurrent by 1" (the end of "the algorithm for processing
/// rows").
pub fn end_row(f: Former) -> Former {
    Former {
        ycurrent: f.ycurrent.saturating_add(1).min(f.yheight),
        ..f
    }
}

/// "The algorithm for ending a row group": "While ycurrent is less than
/// yheight, follow these steps: Run the algorithm for growing
/// downward-growing cells. Increase ycurrent by 1."
pub fn end_group(f: Former) -> Former {
    Former {
        ycurrent: f.yheight,
        ..f
    }
}

/// A cell's place in the merged grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Slot {
    /// The cell box.
    pub cell: BoxId,
    /// Its first column.
    pub col: usize,
    /// The number of columns it spans (at least 1).
    pub cols: usize,
    /// Its first row.
    pub row: usize,
    /// The number of rows it spans (at least 1).
    pub rows: usize,
}

/// The tracks a row, column or group box covers in the merged grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tracks {
    /// The box.
    pub owner: BoxId,
    /// Its first track.
    pub start: usize,
    /// The number of tracks it covers (0 for a group with none).
    pub span: usize,
}

/// The grid of a table box.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Grid {
    /// The number of columns.
    pub columns: usize,
    /// The number of rows.
    pub rows: usize,
    /// Each cell's slot, in the order the algorithm placed them (row by
    /// row, in tree order within a row).
    pub cells: Vec<Slot>,
    /// Each column box's columns.
    pub column_boxes: Vec<Tracks>,
    /// Each column group box's columns.
    pub column_groups: Vec<Tracks>,
    /// Each row box's row.
    pub row_boxes: Vec<Tracks>,
    /// Each row group box's rows.
    pub row_groups: Vec<Tracks>,
    /// Boxes the algorithm skips (column groups after the first row and
    /// their columns): laid out empty.
    pub skipped: Vec<BoxId>,
}

impl Grid {
    /// CSS Tables 3 §3.2: "If the row/column grid has at least one slot";
    /// otherwise "an empty table is laid out", whose width and height are
    /// its captions' and its own `width` and `height` only (no column, row
    /// or border spacing counts).
    pub fn has_slots(&self) -> bool {
        self.columns > 0 && self.rows > 0
    }
}

/// An HTML element's attribute `name` parsed by the rules for parsing
/// non-negative integers, if box `b`'s node is an HTML element named
/// `element` (CSS Tables 3 §3.3.1: "use the attributes of their
/// originating element if and only if it is an HTML element of the same
/// type").
fn number(tree: &BoxTree, arena: &Arena, b: BoxId, element: &[&str], name: &str) -> Option<i64> {
    let node = tree.get(b).and_then(|x| x.node)?;
    if node >= arena.len() || !element.iter().any(|e| is_html(arena, node, e)) {
        return None;
    }
    match arena.kind(node) {
        ExecKind::Element { attributes, .. } => {
            attribute(attributes, name).and_then(non_negative_integer)
        }
        _ => None,
    }
}

/// A `span` attribute (of `col` or `colgroup`): "If the result of parsing
/// the value is not an error or zero, then let span be that value.
/// Otherwise … let span be 1. If span is greater than 1000, let it be 1000
/// instead."
fn span_attribute(value: Option<i64>) -> u32 {
    match value {
        Some(v) if v > 0 => u32::try_from(v.min(1000)).unwrap_or(1),
        _ => 1,
    }
}

/// For each column, the row its latest covering cell reaches (exclusive)
/// and that cell's right edge.
#[derive(Debug, Clone, Copy, Default)]
struct Cover {
    until: u64,
    right: u32,
}

/// The state of the driver: HTML's variables, the covered slots, and what
/// has been placed (in HTML coordinates).
struct Forming<'a> {
    tree: &'a BoxTree,
    arena: &'a Arena,
    f: Former,
    cover: Vec<Cover>,
    cells: Vec<(BoxId, Placed)>,
    /// "The list of downward-growing cells", as indexes into `cells`.
    downward: Vec<usize>,
    columns: Vec<(BoxId, u32, u32)>,
    groups: Vec<(BoxId, u32, u32)>,
    /// The column groups with no column boxes.
    lone_groups: Vec<(BoxId, u32, u32)>,
    rows: Vec<(BoxId, u64)>,
    row_groups: Vec<(BoxId, u64, u64)>,
}

impl Forming<'_> {
    /// "The algorithm for processing rows" for row box `row`.
    fn row(&mut self, row: BoxId) {
        self.f = start_row(self.f);
        // 3. "Run the algorithm for growing downward-growing cells": their
        // cover reaches every row until their group ends (`mod.rs`).
        let y = self.f.ycurrent;
        self.rows.push((row, y));
        let cells: Vec<BoxId> = self
            .tree
            .children(row)
            .iter()
            .copied()
            .filter(|&c| self.tree.class(c) == Class::Cell)
            .collect();
        // 4. "If the tr element being processed has no td or th element
        // children, then increase ycurrent by 1, abort this set of steps".
        for cell in cells {
            // 6. "Cells: While xcurrent is less than xwidth and the slot
            // with coordinate (xcurrent, ycurrent) already has a cell
            // assigned to it, increase xcurrent by 1."
            let mut x = self.f.xcurrent;
            while let Some(c) = self.cover.get(usize::try_from(x).unwrap_or(usize::MAX)) {
                if c.until <= y {
                    break;
                }
                x = c.right.max(x.saturating_add(1));
            }
            // 8 to 11. colspan and rowspan.
            let s = spans(
                number(self.tree, self.arena, cell, &["td", "th"], "colspan"),
                number(self.tree, self.arena, cell, &["td", "th"], "rowspan"),
            );
            // 7, 12 to 15, 19.
            let (p, f) = place(self.f, x, s);
            self.f = f;
            // 18. "If cell grows downward is true, then add the tuple {c,
            // xcurrent, colspan} to the list of downward-growing cells."
            let until = if s.downward {
                self.downward.push(self.cells.len());
                u64::MAX
            } else {
                p.y.saturating_add(u64::from(p.height))
            };
            self.cells.push((cell, p));
            self.cover_columns(p.x, p.width, until);
        }
        // "increase ycurrent by 1".
        self.f = end_row(self.f);
    }

    /// Records that columns `x .. x + width` are covered until row
    /// `until` (keeping a later reach already recorded).
    fn cover_columns(&mut self, x: u32, width: u32, until: u64) {
        let xwidth = usize::try_from(self.f.xwidth).unwrap_or(0);
        if self.cover.len() < xwidth {
            self.cover.resize(xwidth, Cover::default());
        }
        let right = x.saturating_add(width);
        for c in x..right {
            if let Some(slot) = self.cover.get_mut(usize::try_from(c).unwrap_or(usize::MAX))
                && slot.until <= until
            {
                *slot = Cover { until, right };
            }
        }
    }

    /// "The algorithm for ending a row group".
    fn end_group(&mut self) {
        let yheight = self.f.yheight;
        // "Run the algorithm for growing downward-growing cells" until
        // ycurrent reaches yheight: each reaches the group's last row.
        for &i in &self.downward {
            if let Some((_, p)) = self.cells.get_mut(i) {
                let rows = yheight.saturating_sub(p.y).max(1);
                p.height = u32::try_from(rows).unwrap_or(u32::MAX);
                let (x, w) = (p.x, p.width);
                for c in x..x.saturating_add(w) {
                    if let Some(slot) = self.cover.get_mut(usize::try_from(c).unwrap_or(usize::MAX))
                        && slot.until == u64::MAX
                    {
                        slot.until = yheight;
                    }
                }
            }
        }
        // "Empty the list of downward-growing cells."
        self.downward.clear();
        self.f = end_group(self.f);
    }

    /// "The algorithm for processing row groups" for row group box `g`.
    fn row_group(&mut self, g: BoxId) {
        // 1. "Let ystart have the value of yheight."
        let ystart = self.f.yheight;
        // 2. "For each tr element that is a child of the element being
        // processed, in tree order, run the algorithm for processing rows."
        let rows: Vec<BoxId> = self
            .tree
            .children(g)
            .iter()
            .copied()
            .filter(|&r| self.tree.class(r) == Class::Row)
            .collect();
        for r in rows {
            self.row(r);
        }
        // 3. "If yheight > ystart, then let all the last rows in the table
        // from y=ystart to y=yheight-1 form a new row group".
        self.row_groups.push((g, ystart, self.f.yheight));
        // 4. "Run the algorithm for ending a row group."
        self.end_group();
    }

    /// The "Column groups" steps for column group box `g`.
    fn column_group(&mut self, g: BoxId) {
        let cols: Vec<BoxId> = self
            .tree
            .children(g)
            .iter()
            .copied()
            .filter(|&c| self.tree.class(c) == Class::Column)
            .collect();
        // "Let xstart have the value of xwidth."
        let xstart = self.f.xwidth;
        if cols.is_empty() {
            // "If the current element has no col element children": its own
            // `span`.
            let span = span_attribute(number(self.tree, self.arena, g, &["colgroup"], "span"));
            let start = self.f.xwidth;
            self.grow(span);
            let entry = (g, start, self.f.xwidth.saturating_sub(start));
            self.groups.push(entry);
            self.lone_groups.push(entry);
            return;
        }
        for c in cols {
            // "Columns: If the current column col element has a span
            // attribute …". "Increase xwidth by span. Let the last span
            // columns in the table correspond to the current column col
            // element."
            let span = span_attribute(number(self.tree, self.arena, c, &["col"], "span"));
            let start = self.f.xwidth;
            self.grow(span);
            self.columns
                .push((c, start, self.f.xwidth.saturating_sub(start)));
        }
        // "Let all the last columns in the table from x=xstart to
        // x=xwidth-1 form a new column group".
        self.groups
            .push((g, xstart, self.f.xwidth.saturating_sub(xstart)));
    }

    /// "Increase xwidth by span", up to the column bound.
    fn grow(&mut self, span: u32) {
        self.f.xwidth = self.f.xwidth.saturating_add(span).min(MAX_COLUMNS);
        self.f.xcurrent = self.f.xcurrent.min(self.f.xwidth);
    }
}

/// The sorted, distinct boundaries of tracks that survive merging, and the
/// merged index of HTML track `t` among them.
fn merged_index<T: Ord + Copy>(bounds: &[T], t: T) -> usize {
    bounds.partition_point(|&b| b <= t).saturating_sub(1)
}

/// The grid of table box `table` of `tree` (built from `arena`), merging
/// columns unless the table is in fixed layout (`fixed`).
pub fn form(tree: &BoxTree, arena: &Arena, table: BoxId, fixed: bool) -> Grid {
    let mut st = Forming {
        tree,
        arena,
        f: Former::START,
        cover: Vec::new(),
        cells: Vec::new(),
        downward: Vec::new(),
        columns: Vec::new(),
        groups: Vec::new(),
        lone_groups: Vec::new(),
        rows: Vec::new(),
        row_groups: Vec::new(),
    };
    let children = tree.children(table);
    // CSS 2.1 §17.2: the first header group and the first footer group.
    let group_of = |c: BoxId| match tree.get(c).map(|x| &x.kind) {
        Some(BoxKind::RowGroup(g)) => Some(*g),
        _ => None,
    };
    let header = children
        .iter()
        .copied()
        .find(|&c| group_of(c) == Some(RowGroup::Header));
    let footer = children
        .iter()
        .copied()
        .find(|&c| group_of(c) == Some(RowGroup::Footer));
    let mut skipped: Vec<BoxId> = Vec::new();
    // "Let the current element be the first element child of the table
    // element." The column groups first: "If the current element is a
    // colgroup, follow these substeps", until the first row or row group.
    let mut rest: Vec<BoxId> = Vec::new();
    let mut in_rows = false;
    for &c in children {
        match tree.class(c) {
            Class::ColumnGroup | Class::Column if !in_rows => {
                if tree.class(c) == Class::ColumnGroup {
                    st.column_group(c);
                } else {
                    // A column box directly in the table: a column group of
                    // its own (`mod.rs`).
                    let span = span_attribute(number(tree, arena, c, &["col"], "span"));
                    let start = st.f.xwidth;
                    st.grow(span);
                    st.columns
                        .push((c, start, st.f.xwidth.saturating_sub(start)));
                }
            }
            Class::ColumnGroup | Class::Column => {
                // "Rows: While the current element is not one of the
                // following elements, advance": a later column group is
                // skipped.
                skipped.push(c);
                skipped.extend_from_slice(tree.children(c));
            }
            Class::Row | Class::RowGroup => {
                in_rows = true;
                if Some(c) != header && Some(c) != footer {
                    rest.push(c);
                }
            }
            _ => {}
        }
    }
    let order: Vec<BoxId> = header.into_iter().chain(rest).chain(footer).collect();
    // "Let ycurrent be 0. Let the list of downward-growing cells be an
    // empty list."
    for c in order {
        if tree.class(c) == Class::Row {
            // "If the current element is a tr, then run the algorithm for
            // processing rows".
            st.row(c);
        } else {
            // "Run the algorithm for ending a row group." … "Run the
            // algorithm for processing row groups."
            st.end_group();
            st.row_group(c);
        }
    }
    let xwidth = st.f.xwidth;
    let yheight = st.f.yheight;
    // CSS Tables 3 §3.3.2: the boundaries between tracks that are not
    // merged.
    let mut cb: Vec<u32> = vec![0, xwidth];
    let mut rb: Vec<u64> = vec![0, yheight];
    for (_, p) in &st.cells {
        cb.push(p.x);
        cb.push(p.x.saturating_add(p.width));
        rb.push(p.y);
        rb.push(p.y.saturating_add(u64::from(p.height)));
    }
    if fixed {
        cb.extend(0..xwidth);
    } else {
        // A column box defines its columns, and so does a column group box
        // with no column boxes (its `span` stands for them).
        for &(_, start, span) in st.columns.iter().chain(st.lone_groups.iter()) {
            cb.extend(start..start.saturating_add(span));
        }
    }
    for &(_, y) in &st.rows {
        rb.push(y);
    }
    cb.retain(|&b| b <= xwidth);
    rb.retain(|&b| b <= yheight);
    cb.sort_unstable();
    cb.dedup();
    rb.sort_unstable();
    rb.dedup();
    let columns = cb.len().saturating_sub(1);
    let rows = rb.len().saturating_sub(1);
    let span_of = |bounds: &[u32], start: u32, width: u32| -> (usize, usize) {
        if width == 0 {
            let s = bounds.partition_point(|&b| b < start);
            return (s, 0);
        }
        let first = merged_index(bounds, start);
        let last = merged_index(bounds, start.saturating_add(width).saturating_sub(1));
        (first, last.saturating_sub(first).saturating_add(1))
    };
    let row_span = |start: u64, height: u64| -> (usize, usize) {
        if height == 0 {
            let s = rb.partition_point(|&b| b < start);
            return (s, 0);
        }
        let first = merged_index(&rb, start);
        let last = merged_index(&rb, start.saturating_add(height).saturating_sub(1));
        (first, last.saturating_sub(first).saturating_add(1))
    };
    let cells = st
        .cells
        .iter()
        .map(|&(cell, p)| {
            let (col, cols) = span_of(&cb, p.x, p.width);
            let (row, rows) = row_span(p.y, u64::from(p.height));
            Slot {
                cell,
                col,
                cols,
                row,
                rows,
            }
        })
        .collect();
    let col_tracks = |v: &[(BoxId, u32, u32)]| -> Vec<Tracks> {
        v.iter()
            .map(|&(owner, start, span)| {
                let (start, span) = span_of(&cb, start, span);
                Tracks { owner, start, span }
            })
            .collect()
    };
    let column_boxes = col_tracks(&st.columns);
    let column_groups = col_tracks(&st.groups);
    let row_boxes = st
        .rows
        .iter()
        .map(|&(owner, y)| {
            let (start, span) = row_span(y, 1);
            Tracks {
                owner,
                start,
                span: span.min(1),
            }
        })
        .collect();
    let row_groups = st
        .row_groups
        .iter()
        .map(|&(owner, s, e)| {
            let (start, span) = row_span(s, e.saturating_sub(s));
            Tracks { owner, start, span }
        })
        .collect();
    Grid {
        columns,
        rows,
        cells,
        column_boxes,
        column_groups,
        row_boxes,
        row_groups,
        skipped,
    }
}
