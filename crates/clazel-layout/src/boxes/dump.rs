//! A box tree as text, one box per line, indented by depth: the format of
//! the golden box tree dumps (`tests/golden_boxes.rs`) and of the unit
//! tests.
//!
//! Each line is the box's kind, then the element that generated it as
//! `<name>` (or `(anonymous)`), then what the kind carries: a split inline
//! box's fragment, a text run's text after Phase I (as a Rust string
//! literal, with its `white-space`, `word-break` and `overflow-wrap` when
//! not `normal`), a replaced element's sizing, a marker's text.

use std::fmt::Write as _;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{OverflowWrap, WhiteSpace, WordBreak};

use super::replaced::string;
use super::tree::{BoxKind, BoxTree, RowGroup};

/// The name of the element that generated a box.
fn element(arena: &Arena, node: Option<usize>) -> String {
    match node.filter(|&n| n < arena.len()).map(|n| arena.kind(n)) {
        Some(ExecKind::Element { local_name, .. }) => format!(" <{}>", string(local_name)),
        Some(_) => String::new(),
        None => " (anonymous)".to_owned(),
    }
}

/// One box's line, without its indentation.
fn line(arena: &Arena, kind: &BoxKind, node: Option<usize>) -> String {
    let at = element(arena, node);
    match kind {
        BoxKind::Root => "root".to_owned(),
        BoxKind::Block => format!("block{at}"),
        BoxKind::InlineBlock => format!("inline-block{at}"),
        BoxKind::Inline(f) => {
            let part = match (f.first, f.last) {
                (true, true) => "",
                (true, false) => " first",
                (false, true) => " last",
                (false, false) => " middle",
            };
            format!("inline{at}{part}")
        }
        BoxKind::Text(run) => {
            let text: String = run.units.iter().map(|u| u.ch).collect();
            let mut s = format!("text{at} {text:?}");
            if run.style.white_space != WhiteSpace::Normal {
                let _ = write!(s, " white-space={:?}", run.style.white_space);
            }
            if run.style.word_break != WordBreak::Normal {
                let _ = write!(s, " word-break={:?}", run.style.word_break);
            }
            if run.style.overflow_wrap != OverflowWrap::Normal {
                let _ = write!(s, " overflow-wrap={:?}", run.style.overflow_wrap);
            }
            s
        }
        BoxKind::Replaced { what, inline } => {
            let level = if *inline { "inline" } else { "block" };
            format!("replaced{at} {level} {what:?}")
        }
        BoxKind::Marker(m) => format!("marker{at} {:?}", m.text),
        BoxKind::TableWrapper { inline } => {
            let w = if *inline {
                "inline-table-wrapper"
            } else {
                "table-wrapper"
            };
            format!("{w}{at}")
        }
        BoxKind::Table { inline } => {
            let t = if *inline { "inline-table" } else { "table" };
            format!("{t}{at}")
        }
        BoxKind::RowGroup(g) => {
            let name = match g {
                RowGroup::Header => "table-header-group",
                RowGroup::Body => "table-row-group",
                RowGroup::Footer => "table-footer-group",
            };
            format!("{name}{at}")
        }
        BoxKind::Row => format!("table-row{at}"),
        BoxKind::Cell => format!("table-cell{at}"),
        BoxKind::ColumnGroup => format!("table-column-group{at}"),
        BoxKind::Column => format!("table-column{at}"),
        BoxKind::Caption => format!("table-caption{at}"),
    }
}

/// The tree as text: each box reachable from the root, in tree order, on
/// its own line, indented two spaces per level. Iterative.
pub fn dump(tree: &BoxTree, arena: &Arena) -> String {
    let mut out = String::new();
    let mut stack = vec![(BoxTree::ROOT, 0usize)];
    let mut seen = vec![false; tree.boxes.len()];
    while let Some((id, depth)) = stack.pop() {
        match seen.get_mut(id) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let Some(b) = tree.get(id) else { continue };
        let _ = writeln!(
            out,
            "{}{}",
            "  ".repeat(depth),
            line(arena, &b.kind, b.node)
        );
        let child_depth = depth.saturating_add(1);
        stack.extend(b.children.iter().rev().map(|&c| (c, child_depth)));
    }
    out
}
