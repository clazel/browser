//! Unit tests for block and inline formatting, one or more per rule.
//!
//! Documents are parsed by the HTML tree builder and cascaded by item 5.7's
//! `clazel_style::cascade` with a small user agent sheet ([`UA`]: the
//! `display` values and nothing else, so every margin is the test's own),
//! laid out with [`BoxFont`] (every glyph an em square, ascent 0.8 em,
//! descent 0.2 em, as WPT's Ahem font), so each expected position can be
//! worked out by hand; the comment above each assertion does that. The real
//! user agent sheet and real fonts run in `tests/golden_flow.rs`.

use clazel_dom::exec::Arena;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use clazel_dom::exec::ExecKind;
use clazel_style::cascade::computed::ComputedStyle;
use clazel_style::cascade::hints::attribute;

use super::dump::dump;
use super::fragment::{BoxFragment, LineItem, Rect};
use super::{BoxFont, FragmentTree, Viewport, layout};
use crate::boxes::replaced::string;
use crate::boxes::{BoxId, BoxKind, BoxTree, LayoutBox, StyleFns, build};

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
const UA: &str = "html, body, div, p, center, ul, ol, h1, pre { display: block }
li { display: list-item }
head, style, script, title { display: none }
table { display: table } tbody { display: table-row-group }
tr { display: table-row } td { display: table-cell }
caption { display: table-caption }";

/// A laid-out document.
struct Laid {
    arena: Arena,
    tree: BoxTree,
    frags: FragmentTree,
}

impl Laid {
    fn dump(&self) -> String {
        dump(&self.frags, &self.tree, &self.arena)
    }
}

fn lay(html: &str, width: u16, height: u16) -> Laid {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let arena = parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena;
    let sources = collect(&arena);
    let code: Vec<u32> = UA.chars().map(u32::from).collect();
    let sheets = ua::Sheets {
        ua: StyleSheet::parse(&code),
        ua_quirks: StyleSheet::parse(&[]),
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

/// `n` CSS pixels in 1/64 px.
fn px(n: i32) -> i32 {
    n.saturating_mul(64)
}

/// A rectangle in CSS pixels.
fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect {
        x: px(x),
        y: px(y),
        width: px(w),
        height: px(h),
    }
}

/// The head of a no-quirks test document: a 10px font, so a line is 10px
/// with a baseline 8px below its top.
const STD: &str = "<!DOCTYPE html><style>html { font-size: 10px } body { margin: 0 }</style>";
/// The same head in quirks mode (no doctype).
const QUIRKS: &str = "<style>html { font-size: 10px } body { margin: 0 }</style>";

/// `body` laid out in no-quirks mode, 200 by 100.
fn std(body: &str) -> Laid {
    lay(&format!("{STD}{body}"), 200, 100)
}

/// `body` laid out in quirks mode, 200 by 100.
fn quirks(body: &str) -> Laid {
    lay(&format!("{QUIRKS}{body}"), 200, 100)
}

impl Laid {
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

    /// The fragment of the element with `id`.
    fn frag(&self, id: &str) -> BoxFragment {
        self.frags
            .fragment(self.id(id))
            .cloned()
            .unwrap_or_default()
    }

    /// The border box of the element with `id`.
    fn bb(&self, id: &str) -> Rect {
        self.frag(id).border_box
    }

    /// The line boxes of the element with `id`.
    fn lines(&self, id: &str) -> Vec<super::fragment::LineBox> {
        self.frags.lines_of(self.id(id)).to_vec()
    }

    /// The glyph runs of the element with `id`'s lines, as (first unit's
    /// text, x, baseline), in order.
    fn runs(&self, id: &str) -> Vec<(String, i32, i32)> {
        let mut out = Vec::new();
        for line in self.lines(id) {
            for item in &line.items {
                if let LineItem::Text(r) = item {
                    let text: String = match self.tree.get(r.source).map(|b| &b.kind) {
                        Some(BoxKind::Text(run)) => r
                            .glyphs
                            .iter()
                            .filter_map(|g| run.units.get(g.unit).map(|u| u.ch))
                            .collect(),
                        _ => String::new(),
                    };
                    out.push((text, r.x, r.baseline));
                }
            }
        }
        out
    }
}

// ---- CSS 2.1 §8.3.1, collapsing margins ----

/// "bottom margin of box and top margin of its next in-flow following
/// sibling": the larger of two positive margins.
#[test]
fn siblings_collapse_to_the_larger() {
    let l = std("<div id=a style='height:10px;margin-bottom:20px'></div>\
         <div id=b style='height:10px;margin-top:30px'></div>");
    // 10 + max(20, 30).
    assert_eq!(l.bb("b"), rect(0, 40, 200, 10), "{}", l.dump());
}

/// "the maximum of the absolute values of the negative adjoining margins
/// is deducted from the maximum of the positive adjoining margins".
#[test]
fn negative_margin_is_deducted() {
    let l = std("<div style='height:10px;margin-bottom:20px'></div>\
         <div id=b style='height:10px;margin-top:-5px'></div>");
    assert_eq!(l.bb("b").y, px(25));
    // Hacker News' comment rows: `margin-bottom:-10px` before a 2px top.
    let l = std("<div style='height:10px;margin-bottom:-10px'></div>\
         <div id=b style='height:10px;margin-top:2px'></div>");
    assert_eq!(l.bb("b").y, px(2));
}

/// "If there are no positive margins, the maximum of the absolute values of
/// the adjoining margins is deducted from zero."
#[test]
fn only_negative_margins() {
    let l = std("<div style='height:10px;margin-bottom:-10px'></div>\
         <div id=b style='height:10px;margin-top:-5px'></div>");
    assert_eq!(l.bb("b").y, px(0));
}

/// "top margin of a box and top margin of its first in-flow child", unless
/// "the element has no top border, no top padding" fails.
#[test]
fn parent_and_first_child_top() {
    let l = std(
        "<div id=p style='margin-top:10px'><div id=c style='margin-top:20px;height:5px'></div></div>",
    );
    assert_eq!(l.bb("p").y, px(20), "{}", l.dump());
    assert_eq!(l.bb("c").y, px(20));
    let l = std(
        "<div id=p style='margin-top:10px;padding-top:1px'><div id=c style='margin-top:20px;height:5px'></div></div>",
    );
    assert_eq!(l.bb("p").y, px(10));
    assert_eq!(l.bb("c").y, px(31));
    let l = std(
        "<div id=p style='margin-top:10px;border-top:1px solid'><div id=c style='margin-top:20px;height:5px'></div></div>",
    );
    assert_eq!(l.bb("c").y, px(31));
}

/// "bottom margin of a last in-flow child and bottom margin of its parent
/// if the parent has 'auto' computed height", and the bullet's "a
/// 'min-height' of zero".
#[test]
fn last_child_and_parent_bottom() {
    let doc = |p: &str| {
        std(&format!(
            "<div id=p style='{p}'><div style='height:5px;margin-bottom:20px'></div></div>\
             <div id=n style='height:1px'></div>"
        ))
    };
    let l = doc("");
    // The child's 20px collapse through the parent's bottom.
    assert_eq!((l.bb("p").height, l.bb("n").y), (px(5), px(25)));
    let l = doc("height:10px");
    // A given height: the child's margin stays inside (and overflows).
    assert_eq!((l.bb("p").height, l.bb("n").y), (px(10), px(10)));
    let l = doc("min-height:1px");
    // §10.6.3 rule 2: the content ends after the child's bottom margin.
    assert_eq!((l.bb("p").height, l.bb("n").y), (px(25), px(25)));
    let l = doc("padding-bottom:1px");
    assert_eq!((l.bb("p").height, l.bb("n").y), (px(26), px(26)));
}

/// "top and bottom margins of a box that does not establish a new block
/// formatting context and that has zero computed 'min-height', zero or
/// 'auto' computed 'height', and no in-flow children": its margins and its
/// neighbours' all collapse, and it sits "as if the element had a non-zero
/// bottom border".
#[test]
fn margins_collapse_through_an_empty_box() {
    let l = std("<div style='height:10px;margin-bottom:5px'></div>\
         <div id=e style='margin:10px 0 20px'></div>\
         <div id=b style='height:10px;margin-top:15px'></div>");
    assert_eq!(l.bb("b").y, px(30), "{}", l.dump());
    assert_eq!(l.bb("e"), rect(0, 20, 200, 0));
    // An empty child collapses through too ("all of its in-flow children's
    // margins (if any) collapse"), and so does a block whose only line is
    // empty (§9.4.2).
    let l = std("<div style='height:10px'></div>\
         <div id=e style='margin-top:10px'><div style='margin-bottom:30px'></div><span></span></div>\
         <div id=b style='height:10px'></div>");
    assert_eq!(l.bb("b").y, px(40), "{}", l.dump());
    // A height stops it.
    let l = std("<div style='height:10px'></div>\
         <div id=e style='margin:10px 0;height:1px'></div><div id=b style='height:10px'></div>");
    assert_eq!(l.bb("b").y, px(31));
}

/// "If the element's margins are collapsed with its parent's top margin,
/// the top border edge of the box is defined to be the same as the
/// parent's."
#[test]
fn collapsed_through_at_the_parent_top() {
    let l = std(
        "<div id=p style='margin-top:4px'><div id=e style='margin-top:8px'></div>\
         <div id=c style='height:1px'></div></div>",
    );
    assert_eq!(l.bb("p").y, px(8), "{}", l.dump());
    assert_eq!(l.bb("e").y, px(8));
    assert_eq!(l.bb("c").y, px(8));
}

/// "Margins of elements that establish new block formatting contexts (such
/// as … elements with 'overflow' other than 'visible') do not collapse with
/// their in-flow children"; §10.6.7 then counts the children's margins in
/// the height.
#[test]
fn block_formatting_context_roots_keep_their_margins() {
    let l = std("<div id=p style='overflow:hidden;margin-top:10px'>\
         <div id=c style='margin:20px 0 5px;height:10px'></div></div>");
    assert_eq!(l.bb("p").y, px(10));
    assert_eq!(l.bb("c").y, px(30));
    // §10.6.7: "the bottom margin-edge of the bottommost block-level child".
    assert_eq!(l.bb("p").height, px(35));
}

/// "Margins of inline-block boxes do not collapse (not even with their
/// in-flow children)."
#[test]
fn inline_block_margins_do_not_collapse() {
    let l = std("<div style='height:10px;margin-bottom:10px'></div>\
         <span id=ib style='display:inline-block;margin-top:5px;height:3px;width:3px'></span>");
    // The anonymous block's line is at 20; the inline block's margin box
    // (8px) sits on the baseline (28), so its border box starts at 25.
    assert_eq!(l.bb("ib"), rect(0, 25, 3, 3), "{}", l.dump());
}

/// "Margins of the root element's box do not collapse."
#[test]
fn root_element_margins_do_not_collapse() {
    let l = lay(
        "<!DOCTYPE html><html style='margin-top:10px;font-size:10px'><body style='margin-top:20px'>\
         <div id=d style='height:1px'></div>",
        200,
        100,
    );
    assert_eq!(l.bb("d").y, px(30), "{}", l.dump());
}

// ---- CSS 2.1 §10.3.3, block widths and margins ----

/// Rule 1, "any 'auto' values for 'margin-left' or 'margin-right' are, for
/// the following rules, treated as zero", then rule 2, over-constrained:
/// "the specified value of 'margin-right' is ignored".
#[test]
fn too_wide_means_auto_margins_are_zero() {
    let l = std("<div id=a style='width:250px;margin:0 auto;height:1px'></div>");
    let f = l.frag("a");
    assert_eq!((f.border_box.x, f.border_box.width), (px(0), px(250)));
    assert_eq!(f.margin.right, px(-50));
}

/// Rule 2: all three given; `margin-right` follows from the equality.
#[test]
fn over_constrained_ignores_margin_right() {
    let l = std("<div id=a style='width:100px;margin:0 10px;height:1px'></div>");
    let f = l.frag("a");
    assert_eq!((f.margin.left, f.margin.right), (px(10), px(90)));
}

/// Rule 3, "If there is exactly one value specified as 'auto', its used
/// value follows from the equality."
#[test]
fn one_auto_follows() {
    let l =
        std("<div id=a style='width:100px;margin-left:auto;margin-right:10px;height:1px'></div>");
    assert_eq!(l.bb("a").x, px(90));
}

/// Rule 4, "If 'width' is set to 'auto', any other 'auto' values become
/// '0' and 'width' follows".
#[test]
fn auto_width_fills() {
    let l = std("<div id=a style='margin:0 auto 0 10px;padding:0 5px;height:1px'></div>");
    // 200 - 10 - 0 (auto) = 190 border box, 180 content.
    assert_eq!(l.bb("a"), rect(10, 0, 190, 1));
}

/// Rule 5, "If both 'margin-left' and 'margin-right' are 'auto', their used
/// values are equal."
#[test]
fn auto_margins_centre() {
    let l = std("<div id=a style='width:100px;margin:0 auto;height:1px'></div>");
    assert_eq!(l.bb("a").x, px(50));
}

/// A width that would be negative is zero, and the box is then
/// over-constrained (`widths.rs`).
#[test]
fn negative_auto_width_is_zero() {
    let l = std("<div id=a style='margin:0 100px 0 150px;height:1px'></div>");
    let f = l.frag("a");
    assert_eq!(f.border_box.width, 0);
    assert_eq!(f.margin.right, px(50));
}

/// §10.4: "If the tentative used width is greater than 'max-width' … If the
/// resulting width is smaller than 'min-width'" (min-width wins).
#[test]
fn min_and_max_width() {
    let l = std(
        "<div id=a style='width:150px;max-width:100px;height:1px'></div>\
         <div id=b style='max-width:50px;min-width:80px;height:1px'></div>\
         <div id=c style='max-width:50%;margin-left:auto;height:1px'></div>",
    );
    assert_eq!(l.bb("a").width, px(100));
    assert_eq!(l.bb("b").width, px(80));
    // Applied again with `width: 100px`: rule 3 gives the auto margin 100.
    assert_eq!(l.bb("c"), rect(100, 2, 100, 1));
}

/// HTML §15.2's "align descendants" for `center` (§15.3.3): an
/// over-constrained descendant with both margins given is centred; one
/// with an `auto` margin is not touched.
#[test]
fn center_aligns_descendants() {
    let l = std(
        "<center><div><div id=t style='width:100px;height:1px'></div></div>\
         <div id=u style='width:100px;margin-left:auto;height:1px'></div></center>",
    );
    assert_eq!(l.bb("t").x, px(50), "{}", l.dump());
    assert_eq!(l.bb("u").x, px(100));
    // `div align=right` aligns to the right.
    let l = std("<div align=right><div id=t style='width:100px;height:1px'></div></div>");
    assert_eq!(l.bb("t").x, px(100));
}

// ---- §10.3.9, §10.3.2: inline blocks and replaced elements ----

/// §10.3.5's shrink-to-fit: "min(max(preferred minimum width, available
/// width), preferred width)".
#[test]
fn inline_blocks_shrink_to_fit() {
    let l = std("<div><span id=s style='display:inline-block'>ab cd</span></div>");
    assert_eq!(l.bb("s").width, px(50), "{}", l.dump());
    let l = std(
        "<div><span id=s style='display:inline-block'>ab cd ef gh ij kl mn op qr st uv</span></div>",
    );
    assert_eq!(l.bb("s").width, px(200));
    // An inline block's baseline is its last line box's.
    let l = std("<div id=d>x<span id=s style='display:inline-block'>a<br>b</span></div>");
    assert_eq!(l.bb("s"), rect(10, 0, 10, 20), "{}", l.dump());
    assert_eq!(l.lines("d").first().map(|x| x.baseline), Some(px(18)));
}

/// §10.3.2 and §10.6.2 for the replaced elements of this phase.
#[test]
fn replaced_sizes() {
    let l = lay(
        &format!(
            "{STD}<div id=d><img id=a style='width:30px;height:20px'><img id=b>\
         <iframe id=c></iframe><input id=i size=3></div>"
        ),
        800,
        600,
    );
    assert_eq!((l.bb("a").width, l.bb("a").height), (px(30), px(20)));
    // An image that represents nothing: natural size 0 by 0.
    assert_eq!((l.bb("b").width, l.bb("b").height), (0, 0));
    // No natural size: 300 by 150.
    assert_eq!((l.bb("c").width, l.bb("c").height), (px(300), px(150)));
    // HTML §15.5.6: 3 characters of 10px, plus max - average (0); one line.
    assert_eq!((l.bb("i").width, l.bb("i").height), (px(30), px(10)));
}

// ---- Heights ----

/// §10.6.3: an auto height ends at the last line box or child; §10.7's
/// `min-height` and `max-height`, `min-height` winning.
#[test]
fn heights_and_their_limits() {
    let l = std(
        "<div id=a>x<br>y</div><div id=b style='height:50px;max-height:20px;min-height:30px'></div>",
    );
    assert_eq!(l.bb("a").height, px(20));
    assert_eq!(l.bb("b").height, px(30));
}

/// §10.5: a percentage height of a box whose containing block's height is
/// not given "computes to 'auto'"; the Quirks Mode Standard's §3.5 looks up
/// to the initial containing block instead.
#[test]
fn percentage_heights() {
    let l = std("<div id=d style='height:50%'></div>");
    assert_eq!(l.bb("d").height, 0);
    let l = std("<div style='height:40px'><div id=d style='height:50%'></div></div>");
    assert_eq!(l.bb("d").height, px(20));
    let l = quirks("<div id=d style='height:50%'></div>");
    assert_eq!(l.bb("d").height, px(50), "{}", l.dump());
}

/// The Quirks Mode Standard's §3.6 and §3.7: the `html` element fills the
/// viewport and the `body` fills the `html` element, less their margins.
#[test]
fn html_and_body_fill_the_viewport_in_quirks_mode() {
    let l = quirks("<body id=b style='margin:8px'><div style='height:10px'></div>");
    let html = l
        .frags
        .fragment(1)
        .map(|f| f.border_box)
        .unwrap_or_default();
    assert_eq!(html, rect(0, 0, 200, 100), "{}", l.dump());
    assert_eq!(l.bb("b"), rect(8, 8, 184, 84));
    let l = std("<body id=b style='margin:8px'><div style='height:10px'></div>");
    assert_eq!(l.bb("b").height, px(10));
}

// ---- CSS 2.1 §10.8, line heights ----

/// §10.8.1's example: "The three rules in the example below have the same
/// resultant line height: `line-height: 1.2`, `1.2em`, `120%`".
#[test]
fn line_height_number_em_and_percentage_agree() {
    for lh in ["1.2", "1.2em", "120%"] {
        let l = std(&format!("<div id=d style='line-height:{lh}'>x</div>"));
        assert_eq!(l.bb("d").height, px(12), "{lh}");
    }
}

/// §10.8.1: leading is split above A and below D; `line-height: 20px` puts
/// a 10px font's baseline at 5 + 8.
#[test]
fn half_leading() {
    let l = std("<div id=d style='line-height:20px'>x</div>");
    assert_eq!(l.lines("d").first().map(|x| x.baseline), Some(px(13)));
}

/// The strut (§10.8.1: "as if each line box starts with a zero-width inline
/// box with the element's font and line height properties") and the
/// Quirks Mode Standard's §3.4, which removes it.
#[test]
fn the_strut_and_blocks_ignore_line_height() {
    let doc = "<div id=d style='font-size:20px'><span style='font-size:10px'>x</span></div>";
    assert_eq!(std(doc).bb("d").height, px(20));
    assert_eq!(quirks(doc).bb("d").height, px(10));
    // Text directly in the block is in its anonymous inline box, which has
    // the block's line height in either mode.
    let doc = "<div id=d style='font-size:20px'>y<span style='font-size:10px'>x</span></div>";
    assert_eq!(quirks(doc).bb("d").height, px(20));
}

/// The Quirks Mode Standard's §3.3: an inline box without text and without
/// horizontal borders or padding has "a line-height of zero"; a line with
/// only a 1px image is 1px high (Hacker News' spacer images).
#[test]
fn line_height_calculation_quirk() {
    let doc = "<div id=d><span><img style='width:1px;height:1px'></span></div>";
    assert_eq!(quirks(doc).bb("d").height, px(1), "{}", quirks(doc).dump());
    // No-quirks mode keeps the strut: 8 above the baseline, 2 below.
    assert_eq!(std(doc).bb("d").height, px(10));
    // With padding the span counts again.
    let doc =
        "<div id=d><span style='padding:0 1px'><img style='width:1px;height:1px'></span></div>";
    assert_eq!(quirks(doc).bb("d").height, px(10));
}

/// §10.8.1's `vertical-align` values.
#[test]
fn vertical_align() {
    // A length raises the box: its baseline is 10px above the strut's.
    let l = std("<div id=d>x<span style='vertical-align:10px'>y</span></div>");
    let runs = l.runs("d");
    let base = runs.first().map_or(0, |r| r.2);
    assert_eq!(runs.get(1).map(|r| r.2), Some(base.saturating_sub(px(10))));
    // The line grows to hold it: from 18 above to 2 below the baseline.
    assert_eq!(l.bb("d").height, px(20));
    // `top`: aligned with the line box's top, which it makes 30px high.
    let l = std("<div id=d>x<img id=i style='vertical-align:top;width:1px;height:30px'></div>");
    assert_eq!(l.bb("d").height, px(30));
    assert_eq!(l.bb("i").y, 0);
    // `bottom`: the line grows upwards, so the baseline moves down.
    let l = std("<div id=d>x<img id=i style='vertical-align:bottom;width:1px;height:30px'></div>");
    assert_eq!(l.bb("d").height, px(30));
    assert_eq!(l.lines("d").first().map(|x| x.baseline), Some(px(28)));
    // `middle`: the midpoint at the baseline less half the x-height (8).
    let l = std("<div id=d>x<img id=i style='vertical-align:middle;width:1px;height:20px'></div>");
    // Midpoint at 4 above the baseline: the image spans 14 above to 6 below.
    assert_eq!(l.bb("d").height, px(20));
    assert_eq!(l.bb("i").y, 0);
    // `text-top`: the top at the parent's content area's top (8 above).
    let l =
        std("<div id=d>x<img id=i style='vertical-align:text-top;width:1px;height:20px'></div>");
    assert_eq!(l.bb("d").height, px(20));
    // `super` and `sub`: a third and a fifth of the parent's font size.
    let l = std(
        "<div id=d>x<span style='vertical-align:super'>y</span><span style='vertical-align:sub'>z</span></div>",
    );
    let runs = l.runs("d");
    let base = runs.first().map_or(0, |r| r.2);
    assert_eq!(runs.get(1).map(|r| r.2), Some(base.saturating_sub(213)));
    assert_eq!(runs.get(2).map(|r| r.2), Some(base.saturating_add(128)));
}

/// §9.4.2: an empty line box has zero height.
#[test]
fn empty_lines_are_zero_height() {
    let l = std("<div id=d><span></span></div><div id=n style='height:1px'></div>");
    assert_eq!(l.bb("d").height, 0, "{}", l.dump());
    assert_eq!(l.bb("n").y, 0);
}

/// Lines break at item 5.12's opportunities with the units' advances; a
/// `br` forces a break.
#[test]
fn lines_wrap_and_break() {
    let l = std("<div id=d style='width:50px'>aa bb cc dd</div>");
    let lines = l.lines("d");
    assert_eq!(lines.len(), 2, "{}", l.dump());
    let runs = l.runs("d");
    // Phase II (CSS Text 3 §4.1.2 step 3) removes the space at the end.
    assert_eq!(runs.first().map(|r| r.0.as_str()), Some("aa bb"));
    assert_eq!(
        runs.get(1).map(|r| (r.0.as_str(), r.2)),
        Some(("cc dd", px(18)))
    );
    let l = std("<div id=d>a<br>b</div>");
    assert_eq!(l.lines("d").len(), 2);
}

// ---- §16.1 and §16.2 ----

/// `text-align`: left, right, centre, `justify` drawn as `left`, and a line
/// too long for its box start-aligned.
#[test]
fn text_align() {
    for (a, x) in [
        ("left", 0),
        ("right", 180),
        ("center", 90),
        ("justify", 0),
        ("end", 180),
    ] {
        let l = std(&format!("<div id=d style='text-align:{a}'>ab</div>"));
        assert_eq!(l.runs("d").first().map(|r| r.1), Some(px(x)), "{a}");
    }
    let l = std(
        "<div id=d style='text-align:center;white-space:nowrap'>aaaaaaaaaaaaaaaaaaaaaaaaa</div>",
    );
    assert_eq!(l.runs("d").first().map(|r| r.1), Some(0));
}

/// `text-indent`: the first line only; "the first line of an anonymous
/// block box is only affected if it is the first child of its parent
/// element".
#[test]
fn text_indent() {
    let l = std("<div id=d style='text-indent:20px;width:50px'>aa bb cc</div>");
    let runs = l.runs("d");
    assert_eq!(runs.first().map(|r| r.1), Some(px(20)), "{}", l.dump());
    assert_eq!(runs.get(1).map(|r| r.1), Some(0));
    let l = std("<div id=d style='text-indent:20px'>a<p>b</p>c</div>");
    let all: Vec<_> = l
        .frags
        .lines
        .iter()
        .flat_map(|x| x.items.iter())
        .filter_map(|i| match i {
            LineItem::Text(r) => Some(r.x),
            _ => None,
        })
        .collect();
    // "a" (first child, indented), "b" (its own element, indented), "c"
    // (an anonymous block that is not the first child).
    assert_eq!(all, [px(20), px(20), 0]);
}

/// An inline box's start and end edges take their place in the line
/// (§9.4.2: "Horizontal margins, borders, and padding are respected").
#[test]
fn inline_edges() {
    let l = std("<div id=d>a<span style='padding:0 5px;margin-left:3px'>b</span>c</div>");
    let xs: Vec<i32> = l.runs("d").iter().map(|r| r.1).collect();
    assert_eq!(xs, [0, px(18), px(33)], "{}", l.dump());
}

// ---- Markers, depth ----

/// A list item's marker ends at its content edge, on its first baseline.
#[test]
fn markers_sit_outside() {
    let l = std("<ul style='padding-left:40px'><li id=l>ab</li></ul>");
    let li = l.id("l");
    let marker = l
        .tree
        .children(li)
        .first()
        .and_then(|&m| l.frags.fragment(m).cloned())
        .unwrap_or_default();
    // The marker "• " is two em squares, ending at the content edge (40).
    assert_eq!(marker.border_box, rect(20, 0, 20, 10), "{}", l.dump());
}

// Tables are item 5.15's: their tests are in `table/tests.rs`.

/// No recursion: a box tree 100,000 blocks deep (300 under Miri, where
/// each box costs far more) lays out.
#[test]
fn deep_trees_lay_out_without_recursion() {
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
    let _: Option<&LayoutBox> = tree.get(parent);
    let arena = Arena::new(Vec::new());
    let f = layout(&tree, &arena, &NoStyle, &BoxFont, Viewport::px(800, 600));
    assert_eq!(
        f.boxes.iter().filter(|b| b.is_some()).count(),
        depth.saturating_add(1)
    );
}
