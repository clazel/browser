//! Unit tests for paint, one or more per item kind and rule.
//!
//! As in `flow/tests.rs`: documents are parsed by the HTML tree builder,
//! cascaded by item 5.7 with a small user agent sheet ([`UA`]: `display`
//! values only, so every border, padding and spacing is the test's own) and
//! laid out with [`BoxFont`] (every glyph an em square, ascent 0.8 em,
//! descent 0.2 em), so each expected position is worked out by hand in the
//! comment above its assertion. The documents use a 10px font: a line is
//! 10px high with its baseline 8px below its top, and each character is
//! 10px wide.

use clazel_dom::exec::Arena;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use super::dump::dump as paint_dump;
use super::order::paint;
use super::state::{DisplayList, Item};
use crate::boxes::{BoxTree, build};
use crate::flow::dump::dump;
use crate::flow::fragment::Rect;
use crate::flow::{BoxFont, FragmentTree, Viewport, layout};

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// The user agent sheet of these tests: `display` only, plus the link
/// colour (so links have one).
const UA: &str = "html, body, div, p, center { display: block }
head, style, script, title { display: none }
table { display: table } caption { display: table-caption }
thead { display: table-header-group } tbody { display: table-row-group }
tfoot { display: table-footer-group } tr { display: table-row }
td, th { display: table-cell } col { display: table-column }
colgroup { display: table-column-group }
span.t { display: inline-table }
span.b { display: inline-block }";

struct Laid {
    arena: Arena,
    tree: BoxTree,
    frags: FragmentTree,
    list: DisplayList,
}

fn lay(html: &str, width: u16, height: u16, quirks_sheet: &str) -> Laid {
    lay_at(html, width, height, quirks_sheet, 1)
}

fn lay_at(html: &str, width: u16, height: u16, quirks_sheet: &str, scale: u32) -> Laid {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let arena = parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena;
    let sources = collect(&arena);
    let code: Vec<u32> = UA.chars().map(u32::from).collect();
    let q: Vec<u32> = quirks_sheet.chars().map(u32::from).collect();
    let sheets = ua::Sheets {
        ua: StyleSheet::parse(&code),
        ua_quirks: StyleSheet::parse(&q),
        hints: StyleSheet::parse(&[]),
    };
    let table = cascade_with(
        &sheets,
        &arena,
        &sources,
        Device::screen(u32::from(width), u32::from(height)),
    );
    let tree = build(&arena, &table);
    let frags = layout(&tree, &arena, &table, &BoxFont, Viewport::px(width, height));
    let url: Vec<u32> = "http://example.com/dir/page"
        .chars()
        .map(u32::from)
        .collect();
    let base = clazel_url::url::parse::basic_url_parser(&url, None);
    let list = paint(
        &frags,
        &tree,
        &arena,
        &table,
        &BoxFont,
        base.as_ref(),
        scale,
    );
    Laid {
        arena,
        tree,
        frags,
        list,
    }
}

const STD: &str = "<!DOCTYPE html><style>html { font-size: 10px } body { margin: 0 }</style>";
const QUIRKS: &str = "<style>html { font-size: 10px } body { margin: 0 }</style>";

/// `body` laid out in no-quirks mode, 400 by 300.
fn std(body: &str) -> Laid {
    lay(&format!("{STD}{body}"), 400, 300, "")
}

/// `body` laid out in quirks mode, 400 by 300.
fn quirks(body: &str) -> Laid {
    lay(&format!("{QUIRKS}{body}"), 400, 300, "")
}

/// `n` CSS pixels in 1/64 px.
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

impl Laid {
    fn dump(&self) -> String {
        format!(
            "{}{}",
            dump(&self.frags, &self.tree, &self.arena),
            paint_dump(&self.list)
        )
    }

    /// The items as text, one per line.
    fn items(&self) -> Vec<String> {
        paint_dump(&self.list)
            .lines()
            .skip(1)
            .map(str::to_owned)
            .collect()
    }
}

/// The index of the first item whose text starts with `prefix`.
fn find(items: &[String], prefix: &str) -> usize {
    items
        .iter()
        .position(|i| i.starts_with(prefix))
        .unwrap_or(usize::MAX)
}

// ---- The canvas: §14.2 and E.2 step 1 ----

/// The root's background covers the canvas (the document's extent, here
/// the 400 by 300 viewport) and the root does not paint it again; an
/// `html` root's transparent background gives way to its `body`'s, which
/// then paints none of its own; with neither, the canvas is white.
#[test]
fn the_canvas_background() {
    let l = std("<style>html { background: #0000ff }</style><p>x");
    assert_eq!(
        l.items().first().map(String::as_str),
        Some("fill 0,0 400x300 #ff0000ff"),
        "{}",
        l.dump()
    );
    assert_eq!(
        l.items()
            .iter()
            .filter(|i| i.ends_with("#ff0000ff"))
            .count(),
        1
    );
    let l = std("<body style='background:#00ff00'>x");
    assert_eq!(
        l.items().first().map(String::as_str),
        Some("fill 0,0 400x300 #ff00ff00"),
        "{}",
        l.dump()
    );
    assert_eq!(
        l.items()
            .iter()
            .filter(|i| i.ends_with("#ff00ff00"))
            .count(),
        1
    );
    let l = std("x");
    assert_eq!(
        l.items().first().map(String::as_str),
        Some("fill 0,0 400x300 #ffffffff")
    );
}

// ---- Backgrounds and borders: §14.2, §8.5 ----

/// A block's background fills its border box; its borders are four solid
/// strips, top and bottom across the box, left and right between them.
/// The div is 400 wide, 2 + 3 + 10 + 3 + 2 = 20 high.
#[test]
fn background_then_four_border_strips() {
    let l = std(
        "<div style='background:#ff0000;border:2px solid #00ff00;padding:3px;border-left-color:#0000ff'>a</div>",
    );
    let items = l.items();
    let at = find(&items, "fill 0,0 400x20 #ffff0000");
    assert!(at < usize::MAX, "{}", l.dump());
    let strips: Vec<&str> = items
        .iter()
        .skip(at + 1)
        .take(4)
        .map(String::as_str)
        .collect();
    assert_eq!(
        strips,
        [
            "fill 0,0 400x2 #ff00ff00",
            "fill 398,2 2x16 #ff00ff00",
            "fill 0,18 400x2 #ff00ff00",
            "fill 0,2 2x16 #ff0000ff",
        ]
    );
}

/// E.2 steps 4 and 7: every block's background before any text, so the
/// second block's background, pulled up 10px by a negative margin, is
/// under the first block's text, not over it.
#[test]
fn backgrounds_before_any_text() {
    let l =
        std("<div id=a style='margin-bottom:-10px'>a</div><div style='background:#ff0000'>b</div>");
    let items = l.items();
    let bg = find(&items, "fill 0,0 400x10 #ffff0000");
    let text = find(&items, "text");
    assert!(bg < text, "{}", l.dump());
}

// ---- Text: E.2 7.2.1.4.1 ----

/// A text item: its glyphs at their 1/64 px pen positions times the scale,
/// in the premultiplied colour (`#ff000080`: alpha 128, red (255 * 128 +
/// 127) / 255 = 128).
#[test]
fn text_items() {
    let l = std("<div style='color:#ff000080;padding-left:5px'>ab</div>");
    let list = &l.list;
    let run = list.items.iter().find_map(|i| match i {
        Item::Text { run, .. } => Some(run.clone()),
        _ => None,
    });
    assert!(run.is_some(), "{}", l.dump());
    let Some(run) = run else { return };
    assert_eq!(run.colour, 0x8080_0000);
    assert_eq!(run.size, px(10));
    // "a" at x = 5, "b" at 15; the baseline is 8.
    let at: Vec<(i32, i32)> = run.glyphs.iter().map(|g| (g.x, g.y)).collect();
    assert_eq!(at, vec![(px(5), px(8)), (px(15), px(8))]);
}

/// Scale 2: every edge doubles, and glyph positions are in 1/64 device px.
#[test]
fn device_scale() {
    let l = lay_at(
        &format!("{STD}<div style='background:#ff0000;width:15px;height:5px'>a</div>"),
        400,
        300,
        "",
        2,
    );
    assert!(
        l.items().contains(&"fill 0,0 30x10 #ffff0000".to_owned()),
        "{}",
        l.dump()
    );
    assert_eq!(
        l.items().first().map(String::as_str),
        Some("fill 0,0 800x600 #ffffffff")
    );
}

// ---- Decorations: §16.3.1 ----

/// Underline under the text, overline over it, then the text, then the
/// line-through over it (E.2 7.2.1.4.1), each 1px thick in the 10px box
/// font: the underline 1px below the baseline (8), the overline at the top
/// of the ascent (0), the line-through half the x-height (8) above the
/// baseline: 8 - 4 = 4.
#[test]
fn decoration_lines() {
    let l =
        std("<div style='text-decoration:underline overline line-through;color:#0000ff'>ab</div>");
    let items = l.items();
    let at = find(&items, "fill 0,9 20x1");
    assert!(at < usize::MAX, "{}", l.dump());
    assert_eq!(
        items.get(at + 1).map(String::as_str),
        Some("fill 0,0 20x1 #ff0000ff")
    );
    assert!(items.get(at + 2).is_some_and(|i| i.starts_with("text")));
    assert_eq!(
        items.get(at + 3).map(String::as_str),
        Some("fill 0,4 20x1 #ff0000ff")
    );
}

/// Decorations reach a span's text in the declaring block's colour, and
/// not an inline block's contents ("nor to the contents of atomic
/// inline-level descendants").
#[test]
fn decorations_propagate_but_not_into_inline_blocks() {
    let l = std(
        "<div style='text-decoration:underline;color:#00ff00'>a<span style='color:#ff0000'>b</span><span class=b>c</span></div>",
    );
    let lines: Vec<String> = l
        .items()
        .into_iter()
        .filter(|i| i.starts_with("fill ") && i.contains(",9 "))
        .collect();
    // "a" and "b" are underlined in green (the div's colour), "c" is not.
    assert_eq!(
        lines,
        ["fill 0,9 10x1 #ff00ff00", "fill 10,9 10x1 #ff00ff00"],
        "{}",
        l.dump()
    );
}

// ---- visibility: §11.2 ----

/// A hidden box paints nothing of its own, but a visible descendant does.
#[test]
fn visibility_hidden() {
    let l = std(
        "<div style='visibility:hidden;background:#ff0000'>a<span style='visibility:visible'>b</span></div>",
    );
    let items = l.items();
    assert!(
        !items.iter().any(|i| i.contains("#ffff0000")),
        "{}",
        l.dump()
    );
    let texts = items.iter().filter(|i| i.starts_with("text")).count();
    assert_eq!(texts, 1);
}

// ---- overflow: §11.1.1 ----

/// `overflow: hidden` clips the box's descendants to its padding box (the
/// border is outside the clip); nested clips are flattened to their
/// intersection, so the list never nests two.
#[test]
fn overflow_clips_are_flat() {
    let l = std(
        "<div style='overflow:hidden;width:50px;height:20px;border:1px solid #000000'>\
         <div style='overflow:hidden;margin-left:30px;width:40px'>abcdefg</div></div>",
    );
    let items = l.items();
    assert!(
        items.contains(&"push-clip 1,1 50x20".to_owned()),
        "{}",
        l.dump()
    );
    // The inner clip: x 31 to 71, cut at 51: 31,1 20x10.
    assert!(
        items.contains(&"push-clip 31,1 20x10".to_owned()),
        "{}",
        l.dump()
    );
    let mut depth = 0i32;
    for i in &items {
        if i.starts_with("push-clip") {
            depth += 1;
        } else if i == "pop-clip" {
            depth -= 1;
        }
        assert!((0..=1).contains(&depth), "{}", l.dump());
    }
    assert_eq!(depth, 0);
}

// ---- Replaced boxes, inline boxes, atomic inlines ----

/// A replaced box paints its border and nothing else (its image is Phase
/// 6's).
#[test]
fn replaced_boxes_paint_only_their_borders() {
    let l = std("<img style='width:20px;height:10px;border:1px solid #ff0000'>");
    let items = l.items();
    let reds = items.iter().filter(|i| i.ends_with("#ffff0000")).count();
    assert_eq!(reds, 4, "{}", l.dump());
    assert_eq!(items.len(), 5);
}

/// An inline box split over two lines: its background on each piece,
/// widened by its vertical padding, and its left border only on the first
/// piece, its right border only on the last.
#[test]
fn inline_box_pieces() {
    let l = std(
        "<div style='width:30px'><span style='background:#ff0000;padding:2px 0;border-left:1px solid #00ff00;border-right:1px solid #0000ff'>aa bb</span></div>",
    );
    let items = l.items();
    let lefts = items.iter().filter(|i| i.ends_with("#ff00ff00")).count();
    let rights = items.iter().filter(|i| i.ends_with("#ff0000ff")).count();
    assert_eq!((lefts, rights), (1, 1), "{}", l.dump());
    // The first piece: the content area 0..10 widened by 2px each way.
    assert!(
        items
            .iter()
            .any(|i| i.starts_with("fill 0,-2 21x14 #ffff0000")),
        "{}",
        l.dump()
    );
}

/// An inline block is painted whole where it sits in its line (E.2
/// 7.2.1.5): after the text before it, before the text after it.
#[test]
fn inline_blocks_paint_in_line_order() {
    let l = std("a<span class=b style='background:#ff0000'>b</span>c");
    let items = l.items();
    let texts: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, i)| i.starts_with("text"))
        .map(|(k, _)| k)
        .collect();
    let bg = find(&items, "fill 10,0 10x10 #ffff0000");
    assert_eq!(texts.len(), 3, "{}", l.dump());
    let t = |k: usize| texts.get(k).copied().unwrap_or(usize::MAX);
    assert!(t(0) < bg && bg < t(1) && t(1) < t(2), "{}", l.dump());
}

// ---- Tables: E.2 step 4, §17.5.1, §17.6.1 ----

/// The table's background, then the row's under each of its cells (not in
/// the 2px spacing), then the cells', then the borders.
#[test]
fn table_layers() {
    let l = std(
        "<table style='border-spacing:2px;background:#0000ff'><tr style='background:#00ff00'>\
         <td style='background:#ff0000'>a</td><td>b</td></tr></table>",
    );
    let items = l.items();
    // The table: 2 + 10 + 2 + 10 + 2 = 26 wide, 2 + 10 + 2 = 14 high.
    let table = find(&items, "fill 0,0 26x14 #ff0000ff");
    let row_a = find(&items, "fill 2,2 10x10 #ff00ff00");
    let row_b = find(&items, "fill 14,2 10x10 #ff00ff00");
    let cell = find(&items, "fill 2,2 10x10 #ffff0000");
    assert!(
        table < row_a && row_a < row_b && row_b < cell,
        "{}",
        l.dump()
    );
    // No row background over the spacing between the cells (x 12 to 14).
    assert!(
        !items
            .iter()
            .any(|i| i.contains("#ff00ff00") && i.starts_with("fill 2,2 22"))
    );
}

// ---- Hit regions ----

/// A link's pieces and boxes give hit regions with its URL resolved against
/// the base URL (`http://example.com/dir/page`), in paint order: the block
/// link's border box comes from E.2 step 4, before the inline links' pieces
/// from step 7. A link whose URL fails gives one with no URL.
#[test]
fn hit_regions() {
    let l = std(
        "<a href='x?y'>ab</a> <a href='http://[' id=bad>c</a> <div><a href='/top' style='display:block'>d</a></div>",
    );
    let hits: Vec<(String, Option<String>)> = l
        .list
        .hits
        .iter()
        .map(|h| {
            (
                format!(
                    "{},{} {}x{}",
                    h.rect.x, h.rect.y, h.rect.width, h.rect.height
                ),
                h.url.clone(),
            )
        })
        .collect();
    assert_eq!(
        hits,
        vec![
            (
                "0,10 400x10".to_owned(),
                Some("http://example.com/top".to_owned())
            ),
            (
                "0,0 20x10".to_owned(),
                Some("http://example.com/dir/x?y".to_owned())
            ),
            ("30,0 10x10".to_owned(), None),
        ],
        "{}",
        l.dump()
    );
}

/// No recursion: blocks nested 100,000 deep (300 under Miri) paint.
#[test]
fn deep_trees_paint_without_recursion() {
    use crate::boxes::{BoxKind, StyleFns};
    use clazel_style::cascade::computed::ComputedStyle;
    struct NoStyle;
    impl StyleFns for NoStyle {
        fn style(&self, _node: usize) -> Option<&ComputedStyle> {
            None
        }
    }
    let depth: usize = if cfg!(miri) { 300 } else { 100_000 };
    let mut tree = BoxTree::new();
    let mut parent = BoxTree::ROOT;
    for _ in 0..depth {
        parent = tree.add_child(parent, BoxKind::Block, None);
    }
    let arena = Arena::new(Vec::new());
    let f = layout(&tree, &arena, &NoStyle, &BoxFont, Viewport::px(800, 600));
    let list = paint(&f, &tree, &arena, &NoStyle, &BoxFont, None, 1);
    // The canvas only: the boxes are transparent and have no borders.
    assert_eq!(list.items.len(), 1);
    let _ = (quirks(""), rect(0, 0, 0, 0));
}
