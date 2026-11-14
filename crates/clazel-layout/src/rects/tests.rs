//! Unit tests for the client rectangles: hand-built fragment trees (the
//! box tree and the document from a parsed page, the fragments written by
//! hand), the JSON round trip, and the comparison's tolerance.

use clazel_dom::exec::Arena;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use super::*;
use crate::boxes::build;
use crate::flow::BoxFont;
use crate::flow::fragment::{BoxFragment, Glyph, GlyphRun, InlinePiece, LineBox};

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn px(n: i32) -> i32 {
    n.saturating_mul(64)
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect {
        x: px(x),
        y: px(y),
        width: px(w),
        height: px(h),
    }
}

/// `<p>ab<b>cd</b></p>` parsed and built into boxes under a `display`-only
/// sheet, with the 10px box font.
fn document() -> (Arena, BoxTree, clazel_style::cascade::ComputedTable) {
    let html = "<!DOCTYPE html><style>p { display: block } html, body { display: block } \
                head, style { display: none } * { font-size: 10px }</style><p>ab<b>cd</b></p>";
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let arena = parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena;
    let sources = collect(&arena);
    let sheets = ua::Sheets {
        ua: StyleSheet::parse(&[]),
        ua_quirks: StyleSheet::parse(&[]),
        hints: StyleSheet::parse(&[]),
    };
    let table = cascade_with(&sheets, &arena, &sources, Device::screen(200, 100));
    let tree = build(&arena, &table);
    (arena, tree, table)
}

/// The box of the node at `path`.
fn box_of(tree: &BoxTree, arena: &Arena, path: &str) -> usize {
    let paths = node_paths(arena);
    tree.boxes
        .iter()
        .position(|b| b.node.and_then(|n| paths.get(n)).is_some_and(|p| p == path))
        .unwrap_or(usize::MAX)
}

/// A hand-built fragment tree: the `p` at 10,20 100x30; one line with the
/// `b` piece at 40,25 20x10 (no edges) and two runs, "ab" at x 20 and "cd"
/// at x 40, on baseline 33.
#[test]
fn rects_from_a_hand_built_tree() {
    let (arena, tree, table) = document();
    let paths = node_paths(&arena);
    // The document's `html` is child 1 (after the doctype), `body` its child
    // 1 (after `head`), `p` its child 0; "ab" is the `p`'s child 0, `b` its
    // child 1, and "cd" the `b`'s child 0.
    let p = box_of(&tree, &arena, "1/1/0");
    let ab = box_of(&tree, &arena, "1/1/0/0");
    let b = box_of(&tree, &arena, "1/1/0/1");
    let cd = box_of(&tree, &arena, "1/1/0/1/0");
    assert!(
        p < tree.boxes.len()
            && ab < tree.boxes.len()
            && b < tree.boxes.len()
            && cd < tree.boxes.len()
    );
    let mut frags = FragmentTree {
        boxes: vec![None; tree.boxes.len()],
        nodes: tree.boxes.iter().map(|x| x.node).collect(),
        ..FragmentTree::default()
    };
    if let Some(slot) = frags.boxes.get_mut(p) {
        *slot = Some(BoxFragment {
            border_box: rect(10, 20, 100, 30),
            lines: 0..1,
            ..BoxFragment::default()
        });
    }
    if let Some(slot) = frags.boxes.get_mut(b) {
        *slot = Some(BoxFragment::default());
    }
    let glyphs = |n: usize| {
        (0..n)
            .map(|k| Glyph {
                id: 1,
                x: px(10).saturating_mul(i32::try_from(k).unwrap_or(0)),
                y: 0,
                advance: px(10),
                unit: k,
            })
            .collect::<Vec<_>>()
    };
    let run = |source: usize, x: i32| GlyphRun {
        source,
        face: 0,
        size: px(10),
        x: px(x),
        baseline: px(33),
        glyphs: glyphs(2),
    };
    frags.lines.push(LineBox {
        container: p,
        rect: rect(20, 25, 80, 10),
        baseline: px(33),
        items: vec![
            LineItem::Inline(InlinePiece {
                inline: b,
                rect: rect(40, 25, 20, 10),
                start_edge: true,
                end_edge: true,
            }),
            LineItem::Text(run(ab, 20)),
            LineItem::Text(run(cd, 40)),
        ],
    });
    let rects = client_rects(&frags, &tree, &arena, &table, &BoxFont);
    let simple: Vec<(&str, RectKind, &str, usize, Rect)> = rects
        .iter()
        .map(|r| (r.node.as_str(), r.kind, r.name.as_str(), r.i, r.rect))
        .collect();
    // The box font's ascent is 8 and descent 2: each run spans 33 - 8 = 25
    // to 35.
    assert_eq!(
        simple,
        vec![
            ("1/1/0", RectKind::Element, "p", 0, rect(10, 20, 100, 30)),
            ("1/1/0/0", RectKind::Text, "", 0, rect(20, 25, 20, 10)),
            ("1/1/0/1", RectKind::Element, "b", 0, rect(40, 25, 20, 10)),
            ("1/1/0/1/0", RectKind::Text, "", 0, rect(40, 25, 20, 10)),
        ]
    );
    let _ = paths;
}

/// The JSON round trip: what [`to_json`] writes, [`from_json`] reads back.
#[test]
fn json_round_trip() {
    let rects = vec![
        ClientRect {
            node: "1/1/0".to_owned(),
            kind: RectKind::Element,
            name: "p".to_owned(),
            i: 0,
            rect: Rect {
                x: 640,
                y: 1281,
                width: 6400,
                height: 32,
            },
        },
        ClientRect {
            node: "1/1/0/0".to_owned(),
            kind: RectKind::Text,
            name: String::new(),
            i: 2,
            rect: rect(0, 0, 0, 0),
        },
    ];
    let meta = Meta {
        name: "clazel \"test\"".to_owned(),
        version: "0.0.0".to_owned(),
        date: "2026-11-13".to_owned(),
        viewport: (800, 600, 1),
    };
    let json = to_json(&rects, &meta);
    assert_eq!(
        from_json(&json),
        Some(("clazel \"test\"".to_owned(), rects))
    );
    // A browser's floats round to the nearest 1/64 px.
    let theirs = "{\"schema\":\"clazel-client-rects/1\",\"engine\":{\"name\":\"chrome\",\"version\":\"1\",\"date\":\"x\"},\
                  \"viewport\":{\"width\":800,\"height\":600,\"scale\":1},\
                  \"rects\":[{\"node\":\"0\",\"kind\":\"text\",\"i\":0,\"x\":8.333333,\"y\":1e-7,\"w\":10,\"h\":-0.5}]}";
    let read = from_json(theirs).map(|(_, r)| r.first().map(|r| r.rect));
    assert_eq!(
        read,
        Some(Some(Rect {
            x: 533,
            y: 0,
            width: 640,
            height: -32
        }))
    );
    assert_eq!(from_json("{\"schema\":\"other\",\"rects\":[]}"), None);
}

/// The tolerance: 2 px in position, 2% in width, each at its edge.
#[test]
fn the_tolerance() {
    let reference = rect(100, 100, 100, 10);
    assert!(within(rect(102, 98, 102, 50), reference));
    assert!(!within(
        Rect {
            x: px(102) + 1,
            ..reference
        },
        reference
    ));
    assert!(!within(rect(100, 100, 103, 10), reference));
    // A zero-width reference takes only zero.
    assert!(within(rect(0, 0, 0, 0), rect(0, 0, 0, 0)));
    assert!(!within(rect(0, 0, 1, 0), rect(0, 0, 0, 0)));
}

/// The report: compared, outside, missing and extra, matched by node, kind
/// and index.
#[test]
fn the_report() {
    let r = |node: &str, i: usize, x: i32| ClientRect {
        node: node.to_owned(),
        kind: RectKind::Element,
        name: "div".to_owned(),
        i,
        rect: rect(x, 0, 50, 10),
    };
    let ours = vec![r("0", 0, 0), r("0", 1, 10), r("1", 0, 0), r("2", 0, 0)];
    let theirs = vec![r("0", 0, 1), r("0", 1, 20), r("1", 0, 0), r("3", 0, 0)];
    let rep = compare(&ours, &theirs);
    assert_eq!(
        (rep.compared, rep.outside, rep.missing, rep.extra),
        (3, 1, 1, 1)
    );
    assert_eq!(
        rep.examples.first().map(|e| (e.0.as_str(), e.2)),
        Some(("0", 1))
    );
}
