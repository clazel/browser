//! Unit tests for table layout, one or more per rule.
//!
//! As in `flow/tests.rs`: documents are parsed by the HTML tree builder,
//! cascaded by item 5.7 with a small user agent sheet ([`UA`]: `display`
//! values only, so every border, padding and spacing is the test's own) and
//! laid out with [`BoxFont`] (every glyph an em square, ascent 0.8 em,
//! descent 0.2 em), so each expected position is worked out by hand in the
//! comment above its assertion. The documents use a 10px font: a line is
//! 10px high with its baseline 8px below its top, and each character is
//! 10px wide.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::hints::attribute;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use crate::boxes::replaced::string;
use clazel_style::cascade::computed::ComputedStyle;

use crate::boxes::{BoxId, BoxKind, BoxTree, Class, RowGroup, StyleFns, build};
use crate::flow::dump::dump;
use crate::flow::fragment::{BoxFragment, Rect};
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

/// The user agent sheet of these tests: `display` only.
const UA: &str = "html, body, div, p, center { display: block }
head, style, script, title { display: none }
table { display: table } caption { display: table-caption }
thead { display: table-header-group } tbody { display: table-row-group }
tfoot { display: table-footer-group } tr { display: table-row }
td, th { display: table-cell } col { display: table-column }
colgroup { display: table-column-group }
span.t { display: inline-table }";

struct Laid {
    arena: Arena,
    tree: BoxTree,
    frags: FragmentTree,
}

fn lay(html: &str, width: u16, height: u16, quirks_sheet: &str) -> Laid {
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
    Laid { arena, tree, frags }
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
        dump(&self.frags, &self.tree, &self.arena)
    }

    /// The principal box of the element with `id`.
    fn id(&self, id: &str) -> BoxId {
        let node = (0..self.arena.len()).find(|&x| match self.arena.kind(x) {
            ExecKind::Element { attributes, .. } => {
                attribute(attributes, "id").map(string).as_deref() == Some(id)
            }
            _ => false,
        });
        self.tree
            .boxes
            .iter()
            .position(|b| node.is_some() && b.node == node)
            .unwrap_or(usize::MAX)
    }

    /// The box after the principal box of `id` (a table's table box follows
    /// its wrapper).
    fn next(&self, id: &str) -> BoxFragment {
        self.frags
            .fragment(self.id(id).saturating_add(1))
            .cloned()
            .unwrap_or_default()
    }

    fn frag(&self, id: &str) -> BoxFragment {
        self.frags
            .fragment(self.id(id))
            .cloned()
            .unwrap_or_default()
    }

    fn bb(&self, id: &str) -> Rect {
        self.frag(id).border_box
    }
}

/// A cell's border box width, in 1/64 px.
fn w(l: &Laid, id: &str) -> i32 {
    l.bb(id).width
}

// ---- The grid: HTML §4.9.12.1 and CSS Tables 3 §3.3 ----

/// Two columns, a spanning cell, and 2px of border spacing. Column `a` is
/// "aa" (20px both ways); column `b` is "b b b" (min-content 10, max-content
/// 50). The spanning cell's min-content 40 is within the columns' 30 plus
/// one spacing of 2 to 70: its first product gives 40 - 30 - 2 = 8 to `b`
/// (the only column with max > min), and its max-content 40 adds nothing.
/// GRIDMAX = 20 + 50 + 3 * 2 = 76 < 400, so the table is 76 wide and the
/// columns get their max-content widths: `a` at x = 2, `b` at 2 + 20 + 2 =
/// 24; `c` at x = 2, 20 + 2 + 50 = 72 wide. Rows: y = 2 and 2 + 10 + 2 =
/// 14; the table is 2 + 10 + 2 + 10 + 2 = 26 high.
#[test]
fn columns_rows_and_spacing() {
    let l = std(
        "<table id=t style='border-spacing:2px'><tr><td id=a>aa</td><td id=b>b b b</td></tr>\
         <tr><td id=c colspan=2>cccc</td></tr></table>",
    );
    assert_eq!(l.bb("t"), rect(0, 0, 76, 26), "{}", l.dump());
    assert_eq!(l.next("t").border_box, rect(0, 0, 76, 26));
    assert_eq!(l.bb("a"), rect(2, 2, 20, 10));
    assert_eq!(l.bb("b"), rect(24, 2, 50, 10));
    assert_eq!(l.bb("c"), rect(2, 14, 72, 10));
}

/// Track merging (§3.3.2): a table whose only cell spans three columns has
/// one column, so one spacing on each side: 10 + 2 * 2 = 14 wide, not
/// 10 + 4 * 2.
#[test]
fn spanned_columns_merge() {
    let l =
        std("<table id=t style='border-spacing:2px'><tr><td id=m colspan=3>a</td></tr></table>");
    assert_eq!(l.bb("t"), rect(0, 0, 14, 14), "{}", l.dump());
    assert_eq!(l.bb("m"), rect(2, 2, 10, 10));
}

/// ERRATA (§3.8.3): a cell spanning two columns that are empty so far
/// shares its width equally. Columns 0 and 1 stay apart (row 2's cells
/// start and end between them); their span-1 cells are empty (0 wide), so
/// the spanning cell's 40 goes 20 and 20.
#[test]
fn spanning_empty_columns_share_equally() {
    let l = std(
        "<table style='border-spacing:0'><tr><td id=x colspan=2>aaaa</td></tr>\
         <tr><td id=p></td><td id=q></td></tr></table>",
    );
    assert_eq!(l.bb("x"), rect(0, 0, 40, 10), "{}", l.dump());
    assert_eq!(l.bb("p").x, 0);
    assert_eq!(w(&l, "p"), px(20));
    assert_eq!(l.bb("q").x, px(20));
    assert_eq!(w(&l, "q"), px(20));
}

/// `rowspan`: `r` spans two rows and is 30 high; the rows' own cells make
/// them 10 each, so the 30 - 20 = 10 they lack is shared in proportion to
/// their heights, 5 and 5: rows of 15. `s` and `u` stretch to 15.
#[test]
fn rowspan_shares_its_height() {
    let l = std(
        "<table style='border-spacing:0'><tr><td id=r rowspan=2>a<br>b<br>c</td>\
         <td id=s>s</td></tr><tr><td id=u>u</td></tr></table>",
    );
    assert_eq!(l.bb("r"), rect(0, 0, 10, 30), "{}", l.dump());
    assert_eq!(l.bb("s"), rect(10, 0, 10, 15));
    assert_eq!(l.bb("u"), rect(10, 15, 10, 15));
}

/// `rowspan=0` grows to the end of its row group: three rows of 10; the
/// later rows' cells skip its column.
#[test]
fn rowspan_zero_grows_downward() {
    let l = std(
        "<table style='border-spacing:0'><tbody><tr><td id=d rowspan=0>d</td><td>1</td></tr>\
         <tr><td id=two>2</td></tr><tr><td id=three>3</td></tr></tbody>\
         <tbody><tr><td id=after>4</td></tr></tbody></table>",
    );
    assert_eq!(l.bb("d"), rect(0, 0, 10, 30), "{}", l.dump());
    assert_eq!(l.bb("two"), rect(10, 10, 10, 10));
    assert_eq!(l.bb("three"), rect(10, 20, 10, 10));
    // The next group starts below it, in column 0 again.
    assert_eq!(l.bb("after"), rect(0, 30, 10, 10));
}

/// CSS 2.1 §17.2: the header group goes first and the footer group last,
/// wherever they are in the source.
#[test]
fn header_and_footer_groups_move() {
    let l = std(
        "<table style='border-spacing:0'><tfoot><tr><td id=f>f</td></tr></tfoot>\
         <tbody><tr><td id=b>b</td></tr></tbody><thead><tr><td id=h>h</td></tr></thead></table>",
    );
    assert_eq!(l.bb("h").y, 0, "{}", l.dump());
    assert_eq!(l.bb("b").y, px(10));
    assert_eq!(l.bb("f").y, px(20));
}

/// Hostile input: 70 cells of `colspan=1000` would need 70,000 columns.
/// The grid stops at 65,536: the 66th cell is cut there and the last four
/// are placed in the last column; every cell is laid out.
#[test]
fn the_column_bound_keeps_every_cell() {
    let cells = "<td>x</td>".replace("<td>", "<td colspan=1000>").repeat(70);
    let l = std(&format!("<table><tr>{cells}</tr></table>"));
    let laid = l
        .tree
        .boxes
        .iter()
        .enumerate()
        .filter(|(_, b)| b.kind == BoxKind::Cell)
        .filter(|(i, _)| l.frags.fragment(*i).is_some())
        .count();
    assert_eq!(laid, 70);
}

// ---- Column widths: CSS Tables 3 §3.9 ----

/// §3.9.3.2's first rule: a table wider than its columns' max-content
/// widths (10 and 20) gives the excess, 200 - 30 = 170, in proportion to
/// them: floor(170 * 64 * 10 / 30) = 3626/64 px to the first (3626.67
/// rounded down) and the rest, 10880 - 3626 = 7254/64, to the second.
#[test]
fn excess_width_goes_by_max_content() {
    let l = std(
        "<table style='width:200px;border-spacing:0'><tr><td id=a>a</td><td id=b>bb</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), 640 + 3626, "{}", l.dump());
    assert_eq!(w(&l, "b"), 1280 + 7254);
    assert_eq!(w(&l, "a") + w(&l, "b"), px(200));
}

/// A percent-column gets its percentage of the assignable width (50% of
/// 300 = 150); the excess then goes to the auto column (rule 1).
#[test]
fn percent_columns() {
    let l = std(
        "<table style='width:300px;border-spacing:0'><tr><td id=a style='width:50%'>a</td>\
         <td id=b>b</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), px(150), "{}", l.dump());
    assert_eq!(w(&l, "b"), px(150));
}

/// The min-content-specified guess gives a pixel-column its max-content
/// width (30) before an auto column grows: guesses sum 40, 40, 40, 120;
/// 100 lies between the third and fourth, and only the auto column differs
/// between them (10 to 90), so it gets 10 + 60 = 70.
#[test]
fn pixel_columns_before_auto_columns() {
    let l = std(
        "<table style='width:100px;border-spacing:0'><tr><td id=a style='width:30px'>a</td>\
         <td id=b>b b b b b</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), px(30), "{}", l.dump());
    assert_eq!(w(&l, "b"), px(70));
}

/// An auto-width table in 50px: GRIDMIN 30, GRIDMAX 120, so 50 wide. The
/// guesses are 30, 30, 30 and 120: 50 is between the third and the fourth,
/// the excess 20 shared by the columns' (max - min) of 30 and 60: floor(1280
/// * 1920 / 5760) = 426/64 px and 1280 - 426 = 854/64 px.
#[test]
fn widths_between_two_guesses() {
    let l = std(
        "<div style='width:50px'><table style='border-spacing:0'><tr><td id=a>aa aa</td>\
         <td id=b>b b b b</td></tr></table></div>",
    );
    assert_eq!(w(&l, "a"), 1280 + 426, "{}", l.dump());
    assert_eq!(w(&l, "b"), 640 + 854);
}

/// A table's `width` is its border box's (HTML's `box-sizing:
/// border-box`): 100 wide with 5px borders and padding leaves 80 for the
/// column, which starts at 10.
#[test]
fn width_is_the_border_box() {
    let l = std(
        "<table id=t style='width:100px;padding:5px;border:5px solid;border-spacing:0'>\
         <tr><td id=a>a</td></tr></table>",
    );
    assert_eq!(l.bb("t").width, px(100), "{}", l.dump());
    assert_eq!(l.bb("a"), rect(10, 10, 80, 10));
}

/// `width: 50%` of 400 is 200, below `min-width: 300px`: 300.
#[test]
fn min_width_wins() {
    let l = std("<table id=t style='width:50%;min-width:300px'><tr><td>a</td></tr></table>");
    assert_eq!(l.bb("t").width, px(300), "{}", l.dump());
}

/// CAPMIN: a caption's one 80px word makes the table 80 wide, and the
/// caption sits above the table box.
#[test]
fn captions_widen_the_table() {
    let l = std(
        "<table id=t style='border-spacing:0'><caption id=cap>cccccccc</caption>\
         <tr><td id=a>a</td></tr></table>",
    );
    assert_eq!(l.bb("t"), rect(0, 0, 80, 20), "{}", l.dump());
    assert_eq!(l.bb("cap"), rect(0, 0, 80, 10));
    assert_eq!(l.bb("a"), rect(0, 10, 80, 10));
}

/// Auto margins centre a table (CSS 2.1 §17.5.2: "a table can be centered
/// using left and right 'auto' margins"): (400 - 20) / 2 = 190.
#[test]
fn auto_margins_centre_a_table() {
    let l = std("<table id=t style='margin:0 auto;border-spacing:0'><tr><td>aa</td></tr></table>");
    assert_eq!(l.bb("t"), rect(190, 0, 20, 10), "{}", l.dump());
}

/// CSS 2.1 §17.5.2.1: fixed layout ignores content. A first-row cell's
/// `width` sets column 0 (50); the remaining 150 is shared equally (75,
/// 75), however long the content.
#[test]
fn fixed_layout() {
    let l = std(
        "<table style='table-layout:fixed;width:200px;border-spacing:0'><tr>\
         <td id=a style='width:50px'>a</td><td id=b>bbbbbbbbbbbbbbbbbbbb</td><td id=c>c</td>\
         </tr></table>",
    );
    assert_eq!(w(&l, "a"), px(50), "{}", l.dump());
    assert_eq!(w(&l, "b"), px(75));
    assert_eq!(w(&l, "c"), px(75));
    // A column box's `width` comes first.
    let l = std(
        "<table style='table-layout:fixed;width:200px;border-spacing:0'>\
         <colgroup><col style='width:120px'></colgroup><tr>\
         <td id=a style='width:50px'>a</td><td id=b>b</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), px(120), "{}", l.dump());
    assert_eq!(w(&l, "b"), px(80));
    // With `width: auto`, the automatic algorithm: the content counts.
    let l = std(
        "<table style='table-layout:fixed;border-spacing:0'><tr><td id=a>aaaa</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), px(40), "{}", l.dump());
}

/// Fixed layout with no auto column left: the excess goes to the length
/// columns in proportion (§3.9.3.2's fixed-mode rules): 30 and 10 in 80
/// become 60 and 20.
#[test]
fn fixed_layout_excess() {
    let l = std(
        "<table style='table-layout:fixed;width:80px;border-spacing:0'><tr>\
         <td id=a style='width:30px'>a</td><td id=b style='width:10px'>b</td></tr></table>",
    );
    assert_eq!(w(&l, "a"), px(60), "{}", l.dump());
    assert_eq!(w(&l, "b"), px(20));
}

// ---- Heights and vertical alignment: CSS 2.1 §17.5.3 ----

/// Each `vertical-align` in a row 40 high (the four-line cell): `top` gets
/// 30 below, `middle` 15 above and below, `bottom` 30 above, `baseline`
/// (8 from its top, as the tall cell's first line) none above.
#[test]
fn vertical_align_in_a_row() {
    let l = std(
        "<table style='border-spacing:0'><tr><td id=t style='vertical-align:top'>t</td>\
         <td id=m style='vertical-align:middle'>m</td><td id=b style='vertical-align:bottom'>b</td>\
         <td id=bl>x</td><td id=tall>a<br>b<br>c<br>d</td></tr></table>",
    );
    let pad = |id: &str| (l.frag(id).padding.top, l.frag(id).padding.bottom);
    assert_eq!(pad("t"), (0, px(30)), "{}", l.dump());
    assert_eq!(pad("m"), (px(15), px(15)));
    assert_eq!(pad("b"), (px(30), 0));
    assert_eq!(pad("bl"), (0, px(30)));
    for id in ["t", "m", "b", "bl", "tall"] {
        assert_eq!(l.bb(id).height, px(40));
    }
}

/// Baselines line up: the 20px cell's baseline is 16 below its top, the
/// 10px cell's 8, so the row's baseline is 16 and the small cell gets 8
/// above (and 20 - 10 - 8 = 2 below).
#[test]
fn baselines_line_up() {
    let l = std(
        "<table style='border-spacing:0'><tr><td id=big style='font-size:20px'>B</td>\
         <td id=sm>s</td></tr></table>",
    );
    assert_eq!(l.frag("sm").padding.top, px(8), "{}", l.dump());
    assert_eq!(l.frag("sm").padding.bottom, px(2));
    assert_eq!(l.frag("big").first_baseline, l.frag("sm").first_baseline);
    assert_eq!(l.frag("sm").first_baseline, Some(px(16)));
}

/// A row's `height` is a minimum; a cell's `height` is its content box's
/// (no-quirks: 20 + 2 * 5 padding = 30) or its border box's (quirks mode,
/// the Quirks Mode Standard's §3.13: 20, which the content's 10 + 10 does
/// not exceed).
#[test]
fn row_and_cell_heights() {
    let l = std(
        "<table style='border-spacing:0'><tr id=r style='height:30px'><td id=a>a</td></tr></table>",
    );
    assert_eq!(l.bb("r").height, px(30), "{}", l.dump());
    assert_eq!(l.bb("a").height, px(30));
    let cell = "<table style='border-spacing:0'><tr><td id=c style='height:20px;padding:5px'>c</td></tr></table>";
    assert_eq!(std(cell).bb("c").height, px(30));
    assert_eq!(quirks(cell).bb("c").height, px(20));
}

/// §3.10.5: a table's `height` beyond its rows goes to the auto-height
/// rows: 100 - 20 - 10 = 70 more for the second row.
#[test]
fn table_height_fills_auto_rows() {
    let l = std(
        "<table id=t style='height:100px;border-spacing:0'><tr style='height:20px'><td id=a>a</td></tr>\
         <tr><td id=b>b</td></tr></table>",
    );
    assert_eq!(l.bb("t").height, px(100), "{}", l.dump());
    assert_eq!(l.bb("a"), rect(0, 0, 10, 20));
    assert_eq!(l.bb("b"), rect(0, 20, 10, 80));
}

/// An inline table sits on its first row's baseline (§17.4): its wrapper
/// is an atomic inline whose baseline is 8 below its top, as the line's.
#[test]
fn inline_table_baseline() {
    let l = std(
        "<div id=d>x<span class=t id=it style='border-spacing:0'><span id=y style='display:table-cell'>y</span></span></div>",
    );
    assert_eq!(l.bb("it"), rect(10, 0, 10, 10), "{}", l.dump());
    assert_eq!(l.bb("d").height, px(10));
}

// ---- HTML's alignment and the quirks ----

/// `<tr align=center>` aligns its cells' blocks (HTML §15.2's "align
/// descendants"): a 20px block in a 100px cell at 40.
#[test]
fn row_align_centres_blocks() {
    let l = std(
        "<table style='width:100px;border-spacing:0'><tr align=center><td>\
         <div id=d style='width:20px'>x</div></td></tr></table>",
    );
    assert_eq!(l.bb("d").x, px(40), "{}", l.dump());
}

/// The Quirks Mode Standard's §3.10: in quirks mode a table with no row
/// group, caption or column has height 0 and no border; not in no-quirks
/// mode (3px borders, 6 high).
#[test]
fn collapsing_table_quirk() {
    let html = "<table id=e style='border:3px solid'></table>";
    let q = quirks(html);
    assert_eq!(q.next("e").border_box.height, 0, "{}", q.dump());
    assert_eq!(q.next("e").border, crate::flow::Sides::ZERO);
    let s = std(html);
    assert_eq!(s.next("e").border_box.height, px(6), "{}", s.dump());
}

/// The Quirks Mode Standard's §3.9: a `nowrap` cell's `width` (40) is its
/// minimum in quirks mode. In 30px the table overflows to 50 and the cell
/// keeps 40; in no-quirks mode the table is 30 and the cell gets 20 (the
/// guesses' sums are 20, 20, 50 and 50).
#[test]
fn nowrap_cell_width_quirk() {
    let html = "<div style='width:30px'><table style='border-spacing:0'><tr>\
                <td id=n nowrap style='width:40px'>a b c d e f</td><td>x</td></tr></table></div>";
    assert_eq!(w(&quirks(html), "n"), px(40), "{}", quirks(html).dump());
    assert_eq!(w(&std(html), "n"), px(20), "{}", std(html).dump());
}

/// The Quirks Mode Standard's §3.8: no soft wrap opportunity around images
/// in an auto-width cell, so two 20px images make a min-content of 40 in
/// quirks mode and 20 in no-quirks mode, in a 10px container.
#[test]
fn images_do_not_wrap_in_quirks_cells() {
    let html = "<div style='width:10px'><table style='border-spacing:0'><tr><td id=i>\
                <img style='width:20px;height:5px'><img style='width:20px;height:5px'></td></tr>\
                </table></div>";
    assert_eq!(w(&quirks(html), "i"), px(40), "{}", quirks(html).dump());
    assert_eq!(w(&std(html), "i"), px(20), "{}", std(html).dump());
}

/// No recursion: tables nested 100,000 deep (wrapper, table, row group,
/// row and cell each time; 50 under Miri) lay out. The box tree is built
/// directly, as in `flow/tests.rs`: the cascade of a document of nested
/// tables is quadratic (`clazel-style`, outside this item).
#[test]
fn nested_tables_lay_out_without_recursion() {
    struct NoStyle;
    impl StyleFns for NoStyle {
        fn style(&self, _node: usize) -> Option<&ComputedStyle> {
            None
        }
    }
    let depth: usize = if cfg!(miri) { 50 } else { 100_000 };
    let mut tree = BoxTree::new();
    let mut parent = BoxTree::ROOT;
    for _ in 0..depth {
        let w = tree.add_child(parent, BoxKind::TableWrapper { inline: false }, None);
        let t = tree.add_child(w, BoxKind::Table { inline: false }, None);
        let g = tree.add_child(t, BoxKind::RowGroup(RowGroup::Body), None);
        let r = tree.add_child(g, BoxKind::Row, None);
        parent = tree.add_child(r, BoxKind::Cell, None);
    }
    let arena = Arena::new(Vec::new());
    let f = layout(&tree, &arena, &NoStyle, &BoxFont, Viewport::px(800, 600));
    let cells = (0..tree.boxes.len())
        .filter(|&b| tree.class(b) == Class::Cell && f.fragment(b).is_some())
        .count();
    assert_eq!(cells, depth);
}

// ---- The steps on their own ----

/// HTML §4.9.12.1's clamps: `colspan` 0 or an error is 1 and above 1000 is
/// 1000; `rowspan` an error is 1, above 65534 is 65534, and 0 grows
/// downward.
#[test]
fn spans_are_clamped() {
    use super::grid::spans;
    let s = spans(Some(0), None);
    assert_eq!((s.colspan, s.rowspan, s.downward), (1, 1, false));
    let s = spans(Some(5000), Some(70_000));
    assert_eq!((s.colspan, s.rowspan, s.downward), (1000, 65534, false));
    let s = spans(None, Some(0));
    assert_eq!((s.colspan, s.rowspan, s.downward), (1, 1, true));
    let s = spans(Some(3), Some(2));
    assert_eq!((s.colspan, s.rowspan, s.downward), (3, 2, false));
}

/// The running share gives out exactly its total: 10 among 1, 1, 1 is 3,
/// 3, 4 (floors of 10/3, 20/3, 30/3 differenced), and all-zero weights
/// share equally.
#[test]
fn shares_add_up() {
    use super::distribute::share;
    assert_eq!(share(10, &[1, 1, 1]), vec![3, 3, 4]);
    assert_eq!(share(7, &[0, 0]), vec![3, 4]);
    assert_eq!(share(100, &[1, 3]), vec![25, 75]);
    assert_eq!(share(5, &[]), Vec::<i64>::new());
}
