//! Unit tests for the box tree, one or more per rule.
//!
//! Documents are parsed by the HTML tree builder, and styled by a
//! hand-written table ([`Hand`]) rather than the cascade, as phase-5.md
//! item 5.13 intends ("tested with hand-written tables"): each element's
//! `display` comes from its tag name, as the user agent style sheet would
//! give it, or from its `d` attribute; its `white-space` from `ws`; its
//! `list-style-type` from `lst`; and `d=contents` sets `display: contents`.
//! The real cascade runs in `tests/golden_boxes.rs`.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_style::cascade::computed::{ComputedStyle, Display, ListStyleType, WhiteSpace};
use clazel_style::cascade::hints::attribute;
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use super::anonymous::split_step;
use super::dump::dump;
use super::replaced::string;
use super::state::{Group, Place, SplitEvent, SplitState, group_step};
use super::tree::{BoxKind, BoxTree};
use super::{StyleFns, build};

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena
}

/// A hand-written style table (the module's documentation).
struct Hand {
    styles: Vec<Option<ComputedStyle>>,
    contents: Vec<bool>,
}

fn display(name: &str) -> Option<Display> {
    Some(match name {
        "none" | "head" | "script" | "style" | "title" => Display::None,
        "block" | "html" | "body" | "div" | "p" | "ul" | "ol" | "center" | "form" => Display::Block,
        "list-item" | "li" => Display::ListItem,
        "inline" | "span" | "a" | "b" | "i" | "font" | "br" | "wbr" | "img" | "input"
        | "textarea" | "iframe" => Display::Inline,
        "inline-block" => Display::InlineBlock,
        "table" => Display::Table,
        "inline-table" => Display::InlineTable,
        "table-row-group" | "tbody" => Display::TableRowGroup,
        "table-header-group" | "thead" => Display::TableHeaderGroup,
        "table-footer-group" | "tfoot" => Display::TableFooterGroup,
        "table-row" | "tr" => Display::TableRow,
        "table-cell" | "td" | "th" => Display::TableCell,
        "table-column-group" | "colgroup" => Display::TableColumnGroup,
        "table-column" | "col" => Display::TableColumn,
        "table-caption" | "caption" => Display::TableCaption,
        _ => return None,
    })
}

fn hand(arena: &Arena) -> Hand {
    let mut styles = vec![None; arena.len()];
    let mut contents = vec![false; arena.len()];
    for x in 0..arena.len() {
        let ExecKind::Element {
            local_name,
            attributes,
            ..
        } = arena.kind(x)
        else {
            continue;
        };
        let mut s = ComputedStyle::initial();
        let d = attribute(attributes, "d").map(string);
        if d.as_deref() == Some("contents")
            && let Some(c) = contents.get_mut(x)
        {
            *c = true;
        }
        s.display = d
            .as_deref()
            .and_then(display)
            .or_else(|| display(&string(local_name)))
            .unwrap_or(Display::Inline);
        if let Some(ws) = attribute(attributes, "ws").map(string) {
            s.white_space = match ws.as_str() {
                "pre" => WhiteSpace::Pre,
                "nowrap" => WhiteSpace::Nowrap,
                "pre-wrap" => WhiteSpace::PreWrap,
                "pre-line" => WhiteSpace::PreLine,
                _ => WhiteSpace::Normal,
            };
        }
        s.list_style_type = match attribute(attributes, "lst").map(string).as_deref() {
            Some("none") => ListStyleType::None,
            Some("decimal") => ListStyleType::Named("decimal"),
            Some("lower-roman") => ListStyleType::Named("lower-roman"),
            Some("upper-alpha") => ListStyleType::Named("upper-alpha"),
            Some("square") => ListStyleType::Named("square"),
            _ => ListStyleType::Named("disc"),
        };
        if let Some(slot) = styles.get_mut(x) {
            *slot = Some(s);
        }
    }
    // Text inherits `white-space` in a real cascade; copy it down.
    for x in clazel_style::cascade::tree_order(arena) {
        let parent_ws = arena
            .parent(x)
            .and_then(|p| styles.get(p).cloned().flatten())
            .map(|s| s.white_space);
        let own = matches!(arena.kind(x), ExecKind::Element { attributes, .. }
            if attribute(attributes, "ws").is_some());
        if let (Some(ws), false, Some(Some(s))) = (parent_ws, own, styles.get_mut(x)) {
            s.white_space = ws;
        }
    }
    Hand { styles, contents }
}

impl StyleFns for Hand {
    fn style(&self, node: usize) -> Option<&ComputedStyle> {
        self.styles.get(node).and_then(Option::as_ref)
    }

    fn display_contents(&self, node: usize) -> bool {
        self.contents.get(node).copied().unwrap_or(false)
    }
}

/// The dump of `body`'s box tree, from the `body` box down, without the
/// root and `html` lines and with two levels of indentation removed.
fn boxes(body: &str) -> String {
    let arena = parse(&format!("<!DOCTYPE html><body>{body}"));
    let tree = build(&arena, &hand(&arena));
    check_tree(&tree);
    dump(&tree, &arena)
        .lines()
        .skip(2)
        .map(|l| l.strip_prefix("    ").unwrap_or(l))
        .map(|l| format!("{l}\n"))
        .collect()
}

/// Structural facts every built tree has: compact, parent links agree
/// with child lists, ids in tree order.
fn check_tree(tree: &BoxTree) {
    let order = tree.preorder();
    assert_eq!(order.len(), tree.boxes.len(), "every box reachable");
    for (i, &id) in order.iter().enumerate() {
        assert_eq!(i, id, "ids in tree order");
    }
    for (id, b) in tree.boxes.iter().enumerate() {
        for &c in &b.children {
            assert_eq!(tree.get(c).and_then(|x| x.parent), Some(id));
            assert!(c > id);
        }
    }
}

fn expect(body: &str, expected: &str) {
    let got = boxes(body);
    assert_eq!(
        got, expected,
        "\n{body}\n--- got:\n{got}--- expected:\n{expected}"
    );
}

// --- Box generation (§9.2, §9.2.4, Display 3) ---------------------------

#[test]
fn display_none_generates_nothing() {
    expect(
        "<div>a<span d=none>b<div>c</div></span>d</div>",
        "block <body>\n  block <div>\n    text \"a\"\n    text \"d\"\n",
    );
}

#[test]
fn display_contents_hoists_children() {
    expect(
        "<div><span d=contents>a<b>b</b></span>c</div>",
        "block <body>\n  block <div>\n    text \"a\"\n    inline <b>\n      text \"b\"\n    text \"c\"\n",
    );
    // `contents` on a replaced element is `none`.
    expect(
        "<div><img d=contents>x</div>",
        "block <body>\n  block <div>\n    text \"x\"\n",
    );
}

#[test]
fn text_collapses_across_inlines() {
    // Phase I runs once over the inline formatting context.
    expect(
        "<p>a  <span> b </span>  c</p>",
        "block <body>\n  block <p>\n    text \"a \"\n    inline <span>\n      text \"b \"\n    text \"c\"\n",
    );
    expect(
        "<p ws=pre>a  b\n</p>",
        "block <body>\n  block <p>\n    text \"a  b\\n\" white-space=Pre\n",
    );
}

#[test]
fn white_space_only_content_generates_no_box() {
    // §9.2.2.1: white space collapsed away; Phase II's first line.
    expect(
        "<div> <span> </span> </div>",
        "block <body>\n  block <div>\n    inline <span>\n",
    );
    // Preserved white space stays.
    expect(
        "<div ws=pre> </div>",
        "block <body>\n  block <div>\n    text \" \" white-space=Pre\n",
    );
}

#[test]
fn br_and_wbr() {
    expect(
        "<p>a<br>b<wbr>c</p>",
        "block <body>\n  block <p>\n    text \"a\"\n    text <br> \"\\n\" white-space=Pre\n    text \"b\"\n    text <wbr> \"\\u{200b}\"\n    text \"c\"\n",
    );
}

#[test]
fn replaced_elements() {
    expect(
        "<p><img width=40><img d=block><input size=5><input type=checkbox><input type=SUBMIT>\
         <input><textarea cols=0 rows=7>text</textarea><iframe src=a.html>x</iframe></p>",
        "block <body>\n  block <p>\n    block (anonymous)\n      replaced <img> inline Image\n    \
         replaced <img> block Image\n    block (anonymous)\n      \
         replaced <input> inline Input(Text { chars: 5 })\n      \
         replaced <input> inline Input(Check)\n      replaced <input> inline Input(Button)\n      \
         replaced <input> inline Input(Text { chars: 20 })\n      \
         replaced <textarea> inline TextArea { cols: 20, rows: 7 }\n      \
         replaced <iframe> inline Iframe { src: Some(\"a.html\") }\n",
    );
}

#[test]
fn list_items_get_markers() {
    expect(
        "<ul><li>a<li lst=none>b<li lst=square>c</ul>",
        "block <body>\n  block <ul>\n    block <li>\n      marker <li> \"\u{2022} \"\n      text \"a\"\n    \
         block <li>\n      text \"b\"\n    block <li>\n      marker <li> \"\u{25aa} \"\n      text \"c\"\n",
    );
    // `start` and `value`, and nested lists with their own counters.
    expect(
        "<ol start=3><li lst=decimal>a<li lst=lower-roman>b<ol><li lst=upper-alpha>c\
         <li value=28 lst=upper-alpha>d</ol><li lst=decimal>e</ol>",
        "block <body>\n  block <ol>\n    block <li>\n      marker <li> \"3. \"\n      text \"a\"\n    \
         block <li>\n      marker <li> \"iv. \"\n      block (anonymous)\n        text \"b\"\n      \
         block <ol>\n        block <li>\n          marker <li> \"A. \"\n          text \"c\"\n        \
         block <li>\n          marker <li> \"AB. \"\n          text \"d\"\n    \
         block <li>\n      marker <li> \"5. \"\n      text \"e\"\n",
    );
}

#[test]
fn marker_text() {
    use super::marker::text;
    let named = |n: &'static str, v: i64| text(&ListStyleType::Named(n), v);
    assert_eq!(named("decimal", -3).as_deref(), Some("-3. "));
    assert_eq!(named("decimal-leading-zero", 7).as_deref(), Some("07. "));
    assert_eq!(named("upper-roman", 3999).as_deref(), Some("MMMCMXCIX. "));
    // Out of range: the fallback, decimal.
    assert_eq!(named("lower-roman", 4000).as_deref(), Some("4000. "));
    assert_eq!(named("lower-alpha", 27).as_deref(), Some("aa. "));
    assert_eq!(named("lower-alpha", 0).as_deref(), Some("0. "));
    assert_eq!(named("lower-greek", 25).as_deref(), Some("αα. "));
    assert_eq!(named("hebrew", 5).as_deref(), Some("5. "));
    assert_eq!(text(&ListStyleType::None, 1), None);
    let s: Vec<u32> = "→".chars().map(u32::from).collect();
    assert_eq!(text(&ListStyleType::String(s), 1).as_deref(), Some("→"));
}

// --- §9.2.1.1 anonymous block boxes -------------------------------------

#[test]
fn anonymous_blocks_around_inline_content() {
    // "Some text <P>More text": an anonymous block around "Some text".
    expect(
        "<div>Some text<p>More text</p></div>",
        "block <body>\n  block <div>\n    block (anonymous)\n      text \"Some text\"\n    \
         block <p>\n      text \"More text\"\n",
    );
}

#[test]
fn inline_split_around_block() {
    // The §9.2.1.1 example: `p { display: inline }`, `span { display: block }`.
    expect(
        "<p d=inline>This is anonymous text before the SPAN.<span d=block>This is the content of SPAN.</span>This is anonymous text after the SPAN.</p>",
        "block <body>\n  block (anonymous)\n    inline <p> first\n      \
         text \"This is anonymous text before the SPAN.\"\n  block <span>\n    \
         text \"This is the content of SPAN.\"\n  block (anonymous)\n    inline <p> last\n      \
         text \"This is anonymous text after the SPAN.\"\n",
    );
}

#[test]
fn split_sides_may_be_empty() {
    // "Even if either side is empty".
    expect(
        "<span><div>x</div></span>",
        "block <body>\n  block (anonymous)\n    inline <span> first\n  block <div>\n    text \"x\"\n  \
         block (anonymous)\n    inline <span> last\n",
    );
}

#[test]
fn nested_inlines_split_together() {
    expect(
        "<span>a<b>b<div>x</div>c</b>d</span>",
        "block <body>\n  block (anonymous)\n    inline <span> first\n      text \"a\"\n      \
         inline <b> first\n        text \"b\"\n  block <div>\n    text \"x\"\n  block (anonymous)\n    \
         inline <span> last\n      inline <b> last\n        text \"c\"\n      text \"d\"\n",
    );
    // An inner inline that starts after a block gets its own first
    // fragment inside a middle fragment of the outer one.
    expect(
        "<span><div>x</div><b><div>y</div></b></span>",
        "block <body>\n  block (anonymous)\n    inline <span> first\n  block <div>\n    text \"x\"\n  \
         block (anonymous)\n    inline <span> middle\n      inline <b> first\n  block <div>\n    \
         text \"y\"\n  block (anonymous)\n    inline <span> last\n      inline <b> last\n",
    );
}

#[test]
fn consecutive_blocks_in_an_inline() {
    // No fragment between consecutive blocks; white space between them
    // leaves an empty middle fragment.
    expect(
        "<span>a<div>x</div><div>y</div>b</span>",
        "block <body>\n  block (anonymous)\n    inline <span> first\n      text \"a\"\n  \
         block <div>\n    text \"x\"\n  block <div>\n    text \"y\"\n  block (anonymous)\n    \
         inline <span> last\n      text \"b\"\n",
    );
    expect(
        "<span>a<div>x</div> <div>y</div>b</span>",
        "block <body>\n  block (anonymous)\n    inline <span> first\n      text \"a\"\n  \
         block <div>\n    text \"x\"\n  block (anonymous)\n    inline <span> middle\n  \
         block <div>\n    text \"y\"\n  block (anonymous)\n    inline <span> last\n      text \"b\"\n",
    );
}

#[test]
fn white_space_between_blocks_makes_no_anonymous_block() {
    expect(
        "<div>\n  <p>a</p>\n  <p>b</p>\n</div>",
        "block <body>\n  block <div>\n    block <p>\n      text \"a\"\n    block <p>\n      text \"b\"\n",
    );
}

#[test]
fn inline_block_is_atomic() {
    expect(
        "<div>a <span d=inline-block><div>b</div></span> c</div>",
        "block <body>\n  block <div>\n    text \"a \"\n    inline-block <span>\n      block <div>\n        \
         text \"b\"\n    text \" c\"\n",
    );
}

// --- §17.2.1 anonymous table objects ------------------------------------

#[test]
fn stage_1_1_column_children_removed() {
    expect(
        "<div d=table><div d=table-column>x<span>y</span></div></div>",
        "block <body>\n  table-wrapper <div>\n    table <div>\n      table-column <div>\n",
    );
}

#[test]
fn stage_1_2_column_group_keeps_columns_only() {
    expect(
        "<div d=table><div d=table-column-group>x<div d=table-column></div><span>y</span></div></div>",
        "block <body>\n  table-wrapper <div>\n    table <div>\n      table-column-group <div>\n        \
         table-column <div>\n",
    );
}

#[test]
fn stage_1_3_white_space_in_tabular_containers() {
    // Between cells of a row, and at a row's ends: removed.
    expect(
        "<div d=table-row> <div d=table-cell>a</div> <div d=table-cell>b</div> </div>",
        "block <body>\n  table-wrapper (anonymous)\n    table (anonymous)\n      table-row <div>\n        \
         table-cell <div>\n          text \"a\"\n        table-cell <div>\n          text \"b\"\n",
    );
    // Next to a sibling that is not a proper table descendant: kept, and
    // wrapped with it into an anonymous cell (Phase I keeps it; Phase II
    // removes it at the line's end, in layout).
    expect(
        "<div d=table-row><span>x</span> <div d=table-cell>b</div></div>",
        "block <body>\n  table-wrapper (anonymous)\n    table (anonymous)\n      table-row <div>\n        \
         table-cell (anonymous)\n          inline <span>\n            text \"x\"\n          \
         text \" \"\n        table-cell <div>\n          text \"b\"\n",
    );
}

#[test]
fn stage_1_4_white_space_between_internal_boxes() {
    // In a block, between two cells: removed, so one anonymous row holds
    // both.
    expect(
        "<div><div d=table-cell>a</div> <div d=table-cell>b</div></div>",
        "block <body>\n  block <div>\n    table-wrapper (anonymous)\n      table (anonymous)\n        \
         table-row (anonymous)\n          table-cell <div>\n            text \"a\"\n          \
         table-cell <div>\n            text \"b\"\n",
    );
}

#[test]
fn stage_2_1_table_children_get_rows() {
    // HN's stray text in a table: an anonymous row and cell.
    expect(
        "<div d=table>x<span>y</span><div d=table-row><div d=table-cell>z</div></div></div>",
        "block <body>\n  table-wrapper <div>\n    table <div>\n      table-row (anonymous)\n        \
         table-cell (anonymous)\n          text \"x\"\n          inline <span>\n            text \"y\"\n      \
         table-row <div>\n        table-cell <div>\n          text \"z\"\n",
    );
}

#[test]
fn stage_2_2_row_group_children_get_rows() {
    expect(
        "<div d=table><div d=table-row-group><div d=table-cell>a</div><div d=table-row></div></div></div>",
        "block <body>\n  table-wrapper <div>\n    table <div>\n      table-row-group <div>\n        \
         table-row (anonymous)\n          table-cell <div>\n            text \"a\"\n        \
         table-row <div>\n",
    );
}

#[test]
fn stage_2_3_row_children_get_cells() {
    expect(
        "<div d=table-row>a<div>b</div><div d=table-cell>c</div>d</div>",
        "block <body>\n  table-wrapper (anonymous)\n    table (anonymous)\n      table-row <div>\n        \
         table-cell (anonymous)\n          block (anonymous)\n            text \"a\"\n          \
         block <div>\n            text \"b\"\n        table-cell <div>\n          text \"c\"\n        \
         table-cell (anonymous)\n          text \"d\"\n",
    );
}

#[test]
fn stage_3_1_cells_get_rows() {
    expect(
        "<div><div d=table-cell>a</div><div d=table-cell>b</div>c</div>",
        "block <body>\n  block <div>\n    table-wrapper (anonymous)\n      table (anonymous)\n        \
         table-row (anonymous)\n          table-cell <div>\n            text \"a\"\n          \
         table-cell <div>\n            text \"b\"\n    block (anonymous)\n      text \"c\"\n",
    );
}

#[test]
fn stage_3_2_misparented_children_get_tables() {
    // In an inline: an inline table, an atomic inline.
    expect(
        "<div>a<span><div d=table-row></div><div d=table-caption>c</div></span></div>",
        "block <body>\n  block <div>\n    text \"a\"\n    inline <span>\n      \
         inline-table-wrapper (anonymous)\n        table-caption <div>\n          text \"c\"\n        \
         inline-table (anonymous)\n          table-row <div>\n",
    );
    // A column outside a column group or table.
    expect(
        "<div><div d=table-column></div></div>",
        "block <body>\n  block <div>\n    table-wrapper (anonymous)\n      table (anonymous)\n        \
         table-column <div>\n",
    );
    // A row group in a cell: a table inside the cell.
    expect(
        "<div d=table-cell><div d=table-row-group></div></div>",
        "block <body>\n  table-wrapper (anonymous)\n    table (anonymous)\n      table-row (anonymous)\n        \
         table-cell <div>\n          table-wrapper (anonymous)\n            table (anonymous)\n              \
         table-row-group <div>\n",
    );
}

#[test]
fn html_tables() {
    // HN's `<tr style='height:10px'/>`: the tree builder makes a `tbody`
    // and the row; the row has no cells.
    expect(
        "<table><tr style='height:10px'/><tr><td>a</td></tr></table>",
        "block <body>\n  table-wrapper <table>\n    table <table>\n      table-row-group <tbody>\n        \
         table-row <tr>\n        table-row <tr>\n          table-cell <td>\n            text \"a\"\n",
    );
    // §17.4: captions go into the wrapper, above the table box.
    expect(
        "<table><tr><td>a</td></tr><caption>c</caption></table>",
        "block <body>\n  table-wrapper <table>\n    table-caption <caption>\n      text \"c\"\n    \
         table <table>\n      table-row-group <tbody>\n        table-row <tr>\n          \
         table-cell <td>\n            text \"a\"\n",
    );
}

// --- Steps --------------------------------------------------------------

#[test]
fn group_step_contract() {
    for open in [false, true] {
        for wrapped in [false, true] {
            let (place, next) = group_step(Group { open }, wrapped);
            assert_eq!(place == Place::Keep, !wrapped);
            assert_eq!(place == Place::Open, wrapped && !open);
            assert_eq!(next.open, wrapped);
        }
    }
}

#[test]
fn split_step_keeps_invariant() {
    let events = [
        SplitEvent::Enter,
        SplitEvent::Inline,
        SplitEvent::Block,
        SplitEvent::Exit,
    ];
    for depth in 0..4usize {
        for open in 0..=depth {
            for parted in open..=depth {
                for anonymous in [false, true] {
                    let s = SplitState {
                        depth,
                        open,
                        parted,
                        anonymous,
                    };
                    if !s.invariant() {
                        continue;
                    }
                    for e in events {
                        let (_, after) = split_step(s, e);
                        assert!(after.invariant(), "{s:?} {e:?} -> {after:?}");
                    }
                }
            }
        }
    }
}

// --- Whole documents ----------------------------------------------------

/// A document whose `html` element holds `depth` elements nested in each
/// other, alternately `span` and `div`, around one text node; built
/// through the arena's own operations, innermost first (appending to a
/// parent with no ancestors yet is constant time; the tree builder is
/// quadratic on such nesting).
fn nested(depth: usize) -> Arena {
    let mut arena = Arena::new(Vec::new());
    let element = |name: &str| ExecKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: name.chars().map(u32::from).collect(),
        attributes: Vec::new(),
        template_contents: None,
        form_owner: None,
    };
    let mut inner = arena
        .create(ExecKind::Text {
            data: vec![u32::from('x')],
        })
        .unwrap_or(0);
    for i in 0..depth {
        let name = if i % 2 == 0 { "div" } else { "span" };
        let Some(e) = arena.create(element(name)) else {
            break;
        };
        arena.append(e, inner);
        inner = e;
    }
    if let Some(html) = arena.create(element("html")) {
        arena.append(html, inner);
        arena.append(0, html);
    }
    arena
}

#[test]
fn deep_documents_build_without_recursion() {
    // 100,000 nested elements: a recursive walk would overflow the test
    // thread's stack long before. Under Miri, 300: the walk is the same
    // loop, and Miri interprets each step thousands of times slower.
    let depth = if cfg!(miri) { 300 } else { 100_000 };
    let arena = nested(depth);
    let tree = build(&arena, &hand(&arena));
    check_tree(&tree);
    let texts = tree
        .boxes
        .iter()
        .filter(|b| matches!(&b.kind, BoxKind::Text(r) if !r.units.is_empty()))
        .count();
    assert_eq!(texts, 1);
    // Each `span` holds a `div`, so every `span` is split: its first and
    // last fragments, around the `div`.
    let fragments = tree
        .boxes
        .iter()
        .filter(|b| matches!(b.kind, BoxKind::Inline(_)))
        .count();
    assert_eq!(fragments, depth);
}

#[test]
fn empty_document() {
    let arena = Arena::new(Vec::new());
    let tree = build(&arena, &hand(&arena));
    assert_eq!(dump(&tree, &arena), "root\n");
}
