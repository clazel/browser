//! A fragment tree as text: the format of the golden fragment dumps
//! (`tests/golden_flow.rs`) and of the unit tests.
//!
//! One line per box laid out as a box, in tree order, indented by depth:
//! its kind and element (item 5.13's `boxes::dump` names), its border box
//! as `x,y wxh` in CSS pixels, then its used margins (`m=`), borders (`b=`)
//! and padding (`p=`) as top, right, bottom, left, each only when not all
//! zero. A block container's line boxes follow it, one per line (`line
//! x,y wxh base=b`), each with its items indented below: `text "…"` with
//! its pen position, `inline <name>` pieces with their rectangle and drawn
//! edges, and `atomic` for an atomic inline (whose own line follows in tree
//! order). Lengths are 1/64 px printed exactly as decimal pixels.

use std::fmt::Write as _;

use clazel_dom::exec::{Arena, ExecKind};

use super::fragment::{FragmentTree, LineItem, Rect, Sides};
use crate::boxes::replaced::string;
use crate::boxes::{BoxKind, BoxTree};

/// `v` (1/64 px) as decimal CSS pixels, exactly: 1/64 is 0.015625.
pub fn px(v: i32) -> String {
    let a = i64::from(v).unsigned_abs();
    let whole = a.div_euclid(64);
    let frac = a.rem_euclid(64).saturating_mul(15_625);
    let sign = if v < 0 { "-" } else { "" };
    if frac == 0 {
        format!("{sign}{whole}")
    } else {
        let digits = format!("{frac:06}");
        format!("{sign}{whole}.{}", digits.trim_end_matches('0'))
    }
}

fn rect(r: &Rect) -> String {
    format!("{},{} {}x{}", px(r.x), px(r.y), px(r.width), px(r.height))
}

fn sides(name: &str, s: &Sides) -> String {
    if *s == Sides::ZERO {
        String::new()
    } else {
        format!(
            " {name}={},{},{},{}",
            px(s.top),
            px(s.right),
            px(s.bottom),
            px(s.left)
        )
    }
}

/// The element that generated a box, as item 5.13's dump names it.
fn element(arena: &Arena, node: Option<usize>) -> String {
    match node.filter(|&n| n < arena.len()).map(|n| arena.kind(n)) {
        Some(ExecKind::Element { local_name, .. }) => format!(" <{}>", string(local_name)),
        Some(_) => String::new(),
        None => " (anonymous)".to_owned(),
    }
}

/// A box's kind, as a word.
fn kind(k: &BoxKind) -> &'static str {
    match k {
        BoxKind::Root => "root",
        BoxKind::Block => "block",
        BoxKind::InlineBlock => "inline-block",
        BoxKind::Inline(_) => "inline",
        BoxKind::Text(_) => "text",
        BoxKind::Replaced { .. } => "replaced",
        BoxKind::Marker(_) => "marker",
        BoxKind::TableWrapper { .. } => "table-wrapper",
        BoxKind::Table { .. } => "table",
        BoxKind::RowGroup(_) => "row-group",
        BoxKind::Row => "row",
        BoxKind::Cell => "cell",
        BoxKind::ColumnGroup => "column-group",
        BoxKind::Column => "column",
        BoxKind::Caption => "caption",
    }
}

/// The text a glyph run draws: its units' characters.
fn run_text(tree: &BoxTree, source: usize, units: impl Iterator<Item = usize>) -> String {
    match tree.get(source).map(|b| &b.kind) {
        Some(BoxKind::Text(run)) => units
            .filter_map(|u| run.units.get(u).map(|x| x.ch))
            .collect(),
        Some(BoxKind::Marker(m)) => m.text.clone(),
        _ => String::new(),
    }
}

/// The fragment tree `f` of box tree `tree`, as text. Iterative.
pub fn dump(f: &FragmentTree, tree: &BoxTree, arena: &Arena) -> String {
    let mut out = String::new();
    let mut stack = vec![(BoxTree::ROOT, 0usize)];
    let mut seen = vec![false; tree.boxes.len()];
    while let Some((id, depth)) = stack.pop() {
        match seen.get_mut(id) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let Some(b) = tree.get(id) else { continue };
        let child_depth = depth.saturating_add(1);
        stack.extend(b.children.iter().rev().map(|&c| (c, child_depth)));
        let Some(frag) = f.fragment(id) else { continue };
        if matches!(b.kind, BoxKind::Inline(_)) {
            continue;
        }
        let pad = "  ".repeat(depth);
        let _ = writeln!(
            out,
            "{pad}{}{} {}{}{}{}",
            kind(&b.kind),
            element(arena, b.node),
            rect(&frag.border_box),
            sides("m", &frag.margin),
            sides("b", &frag.border),
            sides("p", &frag.padding),
        );
        for line in f.lines_of(id) {
            let _ = writeln!(
                out,
                "{pad}  line {} base={}",
                rect(&line.rect),
                px(line.baseline)
            );
            for item in &line.items {
                match item {
                    LineItem::Text(r) => {
                        let text = run_text(tree, r.source, r.glyphs.iter().map(|g| g.unit));
                        let text = if matches!(
                            tree.get(r.source).map(|x| &x.kind),
                            Some(BoxKind::Marker(_))
                        ) {
                            text
                        } else {
                            // One character per unit drawn (a unit may have
                            // several glyphs).
                            let mut units: Vec<usize> = r.glyphs.iter().map(|g| g.unit).collect();
                            units.dedup();
                            run_text(tree, r.source, units.into_iter())
                        };
                        let _ = writeln!(
                            out,
                            "{pad}    text {text:?} x={} base={} w={}",
                            px(r.x),
                            px(r.baseline),
                            px(r.glyphs
                                .iter()
                                .fold(0i32, |a, g| a.saturating_add(g.advance)))
                        );
                    }
                    LineItem::Inline(p) => {
                        let node = tree.get(p.inline).and_then(|x| x.node);
                        let mut e = String::new();
                        if p.start_edge {
                            e.push_str(" start");
                        }
                        if p.end_edge {
                            e.push_str(" end");
                        }
                        let _ = writeln!(
                            out,
                            "{pad}    inline{} {}{e}",
                            element(arena, node),
                            rect(&p.rect)
                        );
                    }
                    LineItem::Atomic(a) => {
                        let node = tree.get(*a).and_then(|x| x.node);
                        let _ = writeln!(out, "{pad}    atomic{}", element(arena, node));
                    }
                }
            }
        }
    }
    out
}
