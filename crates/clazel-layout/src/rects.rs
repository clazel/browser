//! Client rectangles of every element and text node, from the fragment tree,
//! as JSON (phase-5.md item 5.25, "Our side dumps the same rectangles from
//! the fragment tree").
//!
//! # The schema (`clazel-client-rects/1`), stated once
//!
//! The reference script (`scripts/reference-rects.mjs`) records the same
//! JSON from a browser's `getClientRects`, and the comparison reads both:
//!
//! ```json
//! {
//!   "schema": "clazel-client-rects/1",
//!   "engine": { "name": "clazel", "version": "0.0.0", "date": "2026-11-13" },
//!   "viewport": { "width": 800, "height": 600, "scale": 1 },
//!   "rects": [
//!     { "node": "0/1/0", "kind": "element", "name": "center", "i": 0,
//!       "x": 8, "y": 8, "w": 784, "h": 160 },
//!     { "node": "0/1/0/0/0/0/1", "kind": "text", "i": 0,
//!       "x": 33.5, "y": 10, "w": 52.25, "h": 13 }
//!   ]
//! }
//! ```
//!
//! - **`node`**: the node's path from the document: each step its index
//!   among its parent's child nodes (DOM `childNodes`, text and comment
//!   nodes counted), joined by `/`. Both engines parse the same bytes with
//!   HTML's parser, so the same node has the same path.
//! - **`kind`**: `element` or `text`; `name` is an element's local name.
//! - **`i`**: the rectangle's index among the node's, in content order (one
//!   per line an inline box or a text node is on).
//! - **`x`, `y`, `w`, `h`**: CSS pixels in document coordinates (a
//!   browser's `getClientRects` plus its scroll offset, which the script
//!   keeps at 0), as JSON numbers; ours are exact (1/64 px is a finite
//!   decimal).
//! - **An element's rectangles** are the border boxes of its fragments: its
//!   box's border box, an inline box's border area on each line (as
//!   `paint` draws it), a table's wrapper box (CSSOM View's rectangles of a
//!   table element are its wrapper's). An element with no box (`display:
//!   none`) has none.
//! - **A text node's rectangles** are its glyphs on each line: from the
//!   first glyph's pen position to the last one's advance, and from the
//!   baseline less the font's ascent to the baseline plus its descent (a
//!   `Range`'s rectangles, CSSOM View, cover the text's content area).
//!   Runs of one text node on one line (one per face) are one rectangle.

use std::fmt::Write as _;

use clazel_dom::exec::{Arena, ExecKind};

use crate::boxes::replaced::string;
use crate::boxes::{BoxKind, BoxTree, StyleFns};
use crate::flow::TextFns;
use crate::flow::dump::px;
use crate::flow::fragment::{FragmentTree, LineItem, Rect, Sides};
use crate::flow::style::box_styles;

/// What a rectangle is of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RectKind {
    /// An element.
    Element,
    /// A text node.
    Text,
}

/// One client rectangle, in 1/64 CSS px.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientRect {
    /// The node's path (the schema's `node`).
    pub node: String,
    /// Element or text.
    pub kind: RectKind,
    /// An element's local name; empty for text.
    pub name: String,
    /// The index among the node's rectangles.
    pub i: usize,
    /// The rectangle.
    pub rect: Rect,
}

/// Every node's path from the document (the schema's `node`), indexed by
/// node id. Iterative.
pub fn node_paths(arena: &Arena) -> Vec<String> {
    let n = arena.len();
    let mut paths = vec![String::new(); n];
    let mut stack: Vec<usize> = vec![0];
    for _ in 0..n.saturating_add(1) {
        let Some(id) = stack.pop() else { break };
        let base = paths.get(id).cloned().unwrap_or_default();
        for (k, &c) in arena.children(id).iter().enumerate() {
            if let Some(p) = paths.get_mut(c) {
                *p = if base.is_empty() {
                    k.to_string()
                } else {
                    format!("{base}/{k}")
                };
            }
            stack.push(c);
        }
    }
    paths
}

/// The client rectangles of every element and text node of `frags`, laid
/// out from `tree` (built from `arena` with `styles`) in `fonts`, in tree
/// order of their boxes.
pub fn client_rects(
    frags: &FragmentTree,
    tree: &BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    fonts: &impl TextFns,
) -> Vec<ClientRect> {
    let paths = node_paths(arena);
    let box_style = box_styles(tree, styles);
    let mut out: Vec<ClientRect> = Vec::new();
    let mut count: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    let mut push = |node: usize, kind: RectKind, rect: Rect, out: &mut Vec<ClientRect>| {
        let name = match arena.kind(node) {
            ExecKind::Element { local_name, .. } => string(local_name),
            _ => String::new(),
        };
        let i = count.entry(node).or_insert(0);
        out.push(ClientRect {
            node: paths.get(node).cloned().unwrap_or_default(),
            kind,
            name,
            i: *i,
            rect,
        });
        *i = i.saturating_add(1);
    };
    // Inline boxes' pieces and text runs, per box, from the lines.
    let mut pieces: std::collections::HashMap<usize, Vec<Rect>> = std::collections::HashMap::new();
    let mut runs: std::collections::HashMap<usize, Vec<Rect>> = std::collections::HashMap::new();
    for line in &frags.lines {
        // The text box of the item just before, on this line.
        let mut last: Option<usize> = None;
        for item in &line.items {
            match item {
                LineItem::Inline(p) => {
                    last = None;
                    let Some(f) = frags.fragment(p.inline) else {
                        continue;
                    };
                    let (pd, bd) = (f.padding, f.border);
                    let pad = Rect {
                        x: p.rect.x,
                        y: p.rect.y.saturating_sub(pd.top),
                        width: p.rect.width,
                        height: p
                            .rect
                            .height
                            .saturating_add(pd.top)
                            .saturating_add(pd.bottom),
                    };
                    let edges = Sides {
                        top: bd.top,
                        right: if p.end_edge { bd.right } else { 0 },
                        bottom: bd.bottom,
                        left: if p.start_edge { bd.left } else { 0 },
                    };
                    pieces.entry(p.inline).or_default().push(pad.outset(&edges));
                }
                LineItem::Text(r) => {
                    if r.glyphs.is_empty() {
                        continue;
                    }
                    let Some(s) = box_style.get(r.source) else {
                        continue;
                    };
                    let m = fonts.metrics(s);
                    let start = r.glyphs.iter().map(|g| g.x).min().unwrap_or(0);
                    let end = r
                        .glyphs
                        .iter()
                        .map(|g| g.x.saturating_add(g.advance))
                        .max()
                        .unwrap_or(0);
                    let rect = Rect {
                        x: r.x.saturating_add(start),
                        y: r.baseline.saturating_sub(m.ascent),
                        width: end.saturating_sub(start).max(0),
                        height: m.ascent.saturating_add(m.descent).max(0),
                    };
                    let list = runs.entry(r.source).or_default();
                    // A second run of the same text, next on the same line
                    // (another face), widens the rectangle.
                    match list.last_mut() {
                        Some(prev) if last == Some(r.source) => {
                            let right = prev.right().max(rect.right());
                            prev.x = prev.x.min(rect.x);
                            prev.width = right.saturating_sub(prev.x);
                        }
                        _ => list.push(rect),
                    }
                    last = Some(r.source);
                }
                LineItem::Atomic(_) => last = None,
            }
        }
    }
    for (b, lb) in tree.boxes.iter().enumerate() {
        let Some(node) = lb.node else { continue };
        if node >= arena.len() {
            continue;
        }
        match &lb.kind {
            BoxKind::Text(_) => {
                for r in runs.remove(&b).unwrap_or_default() {
                    push(node, RectKind::Text, r, &mut out);
                }
            }
            BoxKind::Inline(_) => {
                for r in pieces.remove(&b).unwrap_or_default() {
                    push(node, RectKind::Element, r, &mut out);
                }
            }
            // A marker is its list item's, not an element of its own; a
            // table box's rectangles are its wrapper's.
            BoxKind::Marker(_) | BoxKind::Table { .. } => {}
            _ => {
                if let Some(f) = frags.fragment(b) {
                    push(node, RectKind::Element, f.border_box, &mut out);
                }
            }
        }
    }
    out
}

/// A JSON string literal of `s`.
fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// What the JSON says about the engine and the viewport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    /// The engine's name.
    pub name: String,
    /// Its version.
    pub version: String,
    /// The date, `YYYY-MM-DD`.
    pub date: String,
    /// The viewport in CSS px, and the scale.
    pub viewport: (u32, u32, u32),
}

/// `rects` as the schema's JSON (the module's schema).
pub fn to_json(rects: &[ClientRect], meta: &Meta) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{{");
    let _ = writeln!(out, "  \"schema\": \"clazel-client-rects/1\",");
    let _ = writeln!(
        out,
        "  \"engine\": {{ \"name\": {}, \"version\": {}, \"date\": {} }},",
        json_string(&meta.name),
        json_string(&meta.version),
        json_string(&meta.date)
    );
    let (w, h, s) = meta.viewport;
    let _ = writeln!(
        out,
        "  \"viewport\": {{ \"width\": {w}, \"height\": {h}, \"scale\": {s} }},"
    );
    let _ = writeln!(out, "  \"rects\": [");
    for (k, r) in rects.iter().enumerate() {
        let kind = match r.kind {
            RectKind::Element => "element",
            RectKind::Text => "text",
        };
        let name = if r.kind == RectKind::Element {
            format!(", \"name\": {}", json_string(&r.name))
        } else {
            String::new()
        };
        let comma = if k.saturating_add(1) < rects.len() {
            ","
        } else {
            ""
        };
        let _ = writeln!(
            out,
            "    {{ \"node\": {}, \"kind\": \"{kind}\"{name}, \"i\": {}, \"x\": {}, \"y\": {}, \"w\": {}, \"h\": {} }}{comma}",
            json_string(&r.node),
            r.i,
            px(r.rect.x),
            px(r.rect.y),
            px(r.rect.width),
            px(r.rect.height)
        );
    }
    let _ = writeln!(out, "  ]");
    let _ = writeln!(out, "}}");
    out
}

// ---- The comparison (item 5.25: "geometry first") ----

/// The tolerance in position, stated once and never loosened (phase-5.md
/// 5.25: "2 px in position"): 2 CSS px, in 1/64 px.
pub const POSITION_TOLERANCE: i64 = 2 * 64;

/// The tolerance in width, in percent of the reference's width (phase-5.md
/// 5.25: "2 % in width").
pub const WIDTH_TOLERANCE_PERCENT: i64 = 2;

/// What a comparison found.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Report {
    /// Rectangles present on both sides (same node, kind and index).
    pub compared: usize,
    /// Of those, the ones outside the tolerance.
    pub outside: usize,
    /// The reference's rectangles we do not have.
    pub missing: usize,
    /// Ours the reference does not have.
    pub extra: usize,
    /// The first few outside the tolerance: node, kind, index, and the two
    /// rectangles (ours, then the reference's).
    pub examples: Vec<(String, RectKind, usize, Rect, Rect)>,
}

/// Whether `ours` is within the tolerance of `reference`: its left and top
/// edges within [`POSITION_TOLERANCE`], its width within
/// [`WIDTH_TOLERANCE_PERCENT`] of the reference's. Heights are not
/// compared: engines take a line's content area from different font
/// tables.
pub fn within(ours: Rect, reference: Rect) -> bool {
    let d = |a: i32, b: i32| i64::from(a).saturating_sub(i64::from(b)).saturating_abs();
    let dw = d(ours.width, reference.width);
    let allowed = i64::from(reference.width)
        .abs()
        .saturating_mul(WIDTH_TOLERANCE_PERCENT);
    d(ours.x, reference.x) <= POSITION_TOLERANCE
        && d(ours.y, reference.y) <= POSITION_TOLERANCE
        && dw.saturating_mul(100) <= allowed
}

/// The comparison of our rectangles with a reference engine's (matched by
/// node, kind and index), with the count outside the tolerance.
pub fn compare(ours: &[ClientRect], reference: &[ClientRect]) -> Report {
    let key = |r: &ClientRect| (r.node.clone(), r.kind == RectKind::Text, r.i);
    let theirs: std::collections::HashMap<(String, bool, usize), Rect> =
        reference.iter().map(|r| (key(r), r.rect)).collect();
    let mut report = Report::default();
    let mut seen: std::collections::HashSet<(String, bool, usize)> =
        std::collections::HashSet::new();
    for r in ours {
        let k = key(r);
        match theirs.get(&k) {
            Some(&t) => {
                report.compared = report.compared.saturating_add(1);
                if !within(r.rect, t) {
                    report.outside = report.outside.saturating_add(1);
                    if report.examples.len() < 20 {
                        report
                            .examples
                            .push((r.node.clone(), r.kind, r.i, r.rect, t));
                    }
                }
                seen.insert(k);
            }
            None => report.extra = report.extra.saturating_add(1),
        }
    }
    report.missing = reference.len().saturating_sub(seen.len());
    report
}

// ---- Reading the schema's JSON (our own reader, CLAUDE.md rule 8) ----

/// A JSON token.
#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Open(char),
    Close(char),
    Colon,
    Comma,
    Str(String),
    Num(f64),
    Word(String),
}

/// The tokens of `s`, or `None` if it is not JSON's lexical grammar.
fn tokens(s: &str) -> Option<Vec<Tok>> {
    let mut out = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            '{' | '[' => {
                chars.next();
                out.push(Tok::Open(c));
            }
            '}' | ']' => {
                chars.next();
                out.push(Tok::Close(c));
            }
            ':' => {
                chars.next();
                out.push(Tok::Colon);
            }
            ',' => {
                chars.next();
                out.push(Tok::Comma);
            }
            '"' => {
                chars.next();
                let mut v = String::new();
                loop {
                    match chars.next()? {
                        '"' => break,
                        '\\' => match chars.next()? {
                            'n' => v.push('\n'),
                            't' => v.push('\t'),
                            'r' => v.push('\r'),
                            'b' => v.push('\u{8}'),
                            'f' => v.push('\u{c}'),
                            'u' => {
                                let hex: String = (0..4).filter_map(|_| chars.next()).collect();
                                let code = u32::from_str_radix(&hex, 16).ok()?;
                                v.push(char::from_u32(code).unwrap_or('\u{FFFD}'));
                            }
                            other => v.push(other),
                        },
                        other => v.push(other),
                    }
                }
                out.push(Tok::Str(v));
            }
            '-' | '0'..='9' => {
                let mut v = String::new();
                while let Some(&d) = chars.peek() {
                    if d.is_ascii_digit() || matches!(d, '-' | '+' | '.' | 'e' | 'E') {
                        v.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                out.push(Tok::Num(v.parse().ok()?));
            }
            'a'..='z' => {
                let mut v = String::new();
                while let Some(&d) = chars.peek() {
                    if d.is_ascii_lowercase() {
                        v.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                out.push(Tok::Word(v));
            }
            _ => return None,
        }
    }
    Some(out)
}

/// A CSS pixel value as 1/64 px, rounded to the nearest.
fn to_px64(v: f64) -> Option<i32> {
    let scaled = (v * 64.0).round();
    if scaled.is_finite() && scaled.abs() < 2_147_483_647.0 {
        // In range: exact as an i32.
        format!("{scaled:.0}").parse().ok()
    } else {
        None
    }
}

/// The rectangles of a document in the schema (the module's schema), and
/// its engine's name; `None` if it is not one.
pub fn from_json(s: &str) -> Option<(String, Vec<ClientRect>)> {
    let toks = tokens(s)?;
    let mut engine = String::new();
    let mut rects = Vec::new();
    // The schema is fixed: find `"rects"`, then read its flat objects; the
    // engine's name is the first `"name"` inside `"engine"`.
    let mut k = 0usize;
    let mut schema_ok = false;
    while let Some(t) = toks.get(k) {
        match t {
            Tok::Str(key) if key == "schema" => {
                schema_ok = matches!(toks.get(k.saturating_add(2)), Some(Tok::Str(v)) if v == "clazel-client-rects/1");
            }
            Tok::Str(key) if key == "engine" => {
                // { "name": "…", …
                if let Some(Tok::Str(v)) = toks.get(k.saturating_add(5)) {
                    engine = v.clone();
                }
            }
            Tok::Str(key) if key == "rects" => {
                k = k.saturating_add(3);
                break;
            }
            _ => {}
        }
        k = k.saturating_add(1);
    }
    if !schema_ok {
        return None;
    }
    // Objects until the array's `]`.
    loop {
        match toks.get(k)? {
            Tok::Close(']') => break,
            Tok::Comma => k = k.saturating_add(1),
            Tok::Open('{') => {
                k = k.saturating_add(1);
                let (mut node, mut kind, mut name, mut i) = (None, None, String::new(), None);
                let (mut x, mut y, mut w, mut h) = (None, None, None, None);
                loop {
                    match toks.get(k)? {
                        Tok::Close('}') => {
                            k = k.saturating_add(1);
                            break;
                        }
                        Tok::Comma => k = k.saturating_add(1),
                        Tok::Str(key) => {
                            let value = toks.get(k.saturating_add(2))?;
                            match (key.as_str(), value) {
                                ("node", Tok::Str(v)) => node = Some(v.clone()),
                                ("kind", Tok::Str(v)) => {
                                    kind = match v.as_str() {
                                        "element" => Some(RectKind::Element),
                                        "text" => Some(RectKind::Text),
                                        _ => return None,
                                    }
                                }
                                ("name", Tok::Str(v)) => name = v.clone(),
                                ("i", Tok::Num(v)) => i = format!("{v:.0}").parse().ok(),
                                ("x", Tok::Num(v)) => x = to_px64(*v),
                                ("y", Tok::Num(v)) => y = to_px64(*v),
                                ("w", Tok::Num(v)) => w = to_px64(*v),
                                ("h", Tok::Num(v)) => h = to_px64(*v),
                                _ => {}
                            }
                            k = k.saturating_add(3);
                        }
                        _ => return None,
                    }
                }
                rects.push(ClientRect {
                    node: node?,
                    kind: kind?,
                    name,
                    i: i?,
                    rect: Rect {
                        x: x?,
                        y: y?,
                        width: w?,
                        height: h?,
                    },
                });
            }
            _ => return None,
        }
    }
    Some((engine, rects))
}

#[cfg(test)]
mod tests;
