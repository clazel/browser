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
use crate::boxes::{
    BoxId, BoxKind, BoxTree, Fragment, LayoutBox, RowGroup, StyleFns, TextRun, build,
};
use crate::text::TextStyle;

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
    /// The principal box of the element with `id`; panics naming the id if
    /// the document has no such element or it generated no box.
    fn id(&self, id: &str) -> BoxId {
        let node = (0..self.arena.len()).find(|&x| match self.arena.kind(x) {
            ExecKind::Element { attributes, .. } => {
                attribute(attributes, "id").map(string).as_deref() == Some(id)
            }
            _ => false,
        });
        assert!(node.is_some(), "no element with id={id:?}");
        let found = self
            .tree
            .boxes
            .iter()
            .position(|b| node.is_some() && b.node == node);
        assert!(found.is_some(), "element id={id:?} generated no box");
        found.unwrap_or(usize::MAX)
    }

    /// The fragment of the element with `id`, if it has one (for tests
    /// where "no fragment" is the expected result); panics if there is no
    /// such element or box.
    fn frag_if_any(&self, id: &str) -> Option<BoxFragment> {
        self.frags.fragment(self.id(id)).cloned()
    }

    /// The fragment of the element with `id`; panics naming the id if it
    /// has none.
    fn frag(&self, id: &str) -> BoxFragment {
        let f = self.frag_if_any(id);
        assert!(f.is_some(), "element id={id:?} has no fragment");
        f.unwrap_or_default()
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
    let html = l.frags.fragment(1).map(|f| f.border_box);
    assert_eq!(html, Some(rect(0, 0, 200, 100)), "{}", l.dump());
    assert_eq!(l.bb("b"), rect(8, 8, 184, 84));
    let l = std("<body id=b style='margin:8px'><div style='height:10px'></div>");
    assert_eq!(l.bb("b").height, px(10));
}

/// KNOWN BUG, pinned (suspected; see the README's "A consequence to check"
/// and the report of the test-gap review). In quirks mode the `body` is
/// stretched to fill the `html` element less its margins (Quirks Mode
/// Standard §3.7), and the `html` element to fill the viewport (§3.6). When
/// the `body`'s last child has a bottom margin larger than the `body`'s, the
/// two collapse (CSS 2.1 §8.3.1: the `body`'s computed `height` is `auto`),
/// so the `body`'s used bottom margin is the larger one. We subtract only
/// the `body`'s own margin (8) when stretching it, so the `body` is 16px too
/// tall and the `html` element ends 8px below the viewport (§10.6.7: its
/// content ends at the bottom margin edge of its last child). Chrome, run on
/// `<p>One<p>Two` in an 800 by 600 viewport in quirks mode, gives `html`
/// 600 and `body` 576 high: it subtracts the collapsed margin (8 + 16), so
/// the page exactly fits and does not scroll. Here the viewport is 100 high,
/// the `body`'s margin 8 and its child's bottom margin 16: the browser-like
/// result is `html` 100 and `body` 76; this test pins what we give (108 and
/// 84) and fails when it is fixed, so that it is then replaced by the
/// browser-like assertion.
#[test]
fn known_bug_quirks_body_fill_ignores_the_collapsed_bottom_margin() {
    let l =
        quirks("<body id=b style='margin:8px'><div style='height:10px;margin-bottom:16px'></div>");
    let html = l.frags.fragment(1).map(|f| f.border_box.height);
    // Not the browser-like (px(100), px(76)).
    assert_eq!(
        (html, l.bb("b").height),
        (Some(px(108)), px(84)),
        "{}",
        l.dump()
    );
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
    // The tests below add a 30px image on the baseline (30 above, none
    // below), so the line has 30 above and 2 (the strut's D) below the
    // baseline, and the baseline is 30px from the line top: `top`,
    // `bottom`, `middle`, `text-top` and `text-bottom` then each put the
    // 20px image at a different y.
    let base30 = "<img style='width:1px;height:30px'>";
    let doc = |va: &str| {
        std(&format!(
            "<div id=d>x<img id=i style='vertical-align:{va};width:1px;height:20px'>{base30}</div>"
        ))
    };
    let baseline = |l: &Laid| l.lines("d").first().map(|x| x.baseline);
    // `middle`: "Align the vertical midpoint of the box with the baseline of
    // the parent box plus half the x-height of the parent." The x-height of
    // the Ahem-like font is its ascent, 8, so the midpoint is 4 above the
    // baseline: the image spans 14 above to 6 below; the line is 30 above
    // and 6 below, 36 high, and the image's top is 30 - 14 = 16 down.
    let l = doc("middle");
    assert_eq!(baseline(&l), Some(px(30)), "{}", l.dump());
    assert_eq!(l.bb("d").height, px(36));
    assert_eq!(l.bb("i").y, px(16));
    // `text-top`: "Align the top of the box with the top of the parent's
    // content area": A = 8 above the baseline, so the image's top is 30 - 8
    // = 22 down, and it hangs 12 below the baseline: the line is 30 + 12.
    let l = doc("text-top");
    assert_eq!(baseline(&l), Some(px(30)), "{}", l.dump());
    assert_eq!(l.bb("d").height, px(42));
    assert_eq!(l.bb("i").y, px(22));
    // `text-bottom`: "Align the bottom of the box with the bottom of the
    // parent's content area": D = 2 below the baseline, so the image spans
    // 18 above to 2 below, and its top is 30 - 18 = 12 down; the line is
    // 30 + 2 high.
    let l = doc("text-bottom");
    assert_eq!(baseline(&l), Some(px(30)), "{}", l.dump());
    assert_eq!(l.bb("d").height, px(32));
    assert_eq!(l.bb("i").y, px(12));
    // `bottom`: "Align the bottom of the aligned subtree with the bottom of
    // the line box": the line is 30 + 2 = 32 high, the image's top 12 down
    // (the same as `text-bottom` here); `top` puts it at the line's top.
    let l = doc("bottom");
    assert_eq!((l.bb("d").height, l.bb("i").y), (px(32), px(12)));
    let l = doc("top");
    assert_eq!((l.bb("d").height, l.bb("i").y), (px(32), 0));
    // `text-bottom` and `bottom` differ when something hangs below the
    // baseline: a span lowered 10px has its content area 2 to 12 below the
    // baseline. The line is 18 above (the image) and 12 below, 30 high;
    // `text-bottom` puts the 20px image's top at 0 (18 above the
    // baseline); with `bottom` the line is 20 high instead (below).
    let low = "<span style='vertical-align:-10px'>y</span>";
    let l = std(&format!(
        "<div id=d>x{low}<img id=i style='vertical-align:text-bottom;width:1px;height:20px'></div>"
    ));
    assert_eq!(baseline(&l), Some(px(18)), "{}", l.dump());
    assert_eq!((l.bb("d").height, l.bb("i").y), (px(30), 0));
    let l = std(&format!(
        "<div id=d>x{low}<img id=i style='vertical-align:bottom;width:1px;height:20px'></div>"
    ));
    // `bottom` does not count towards the line's extent: 8 above (strut)
    // and 12 below make it 20 high, which the 20px image fills.
    assert_eq!((l.bb("d").height, l.bb("i").y), (px(20), 0));
    // `baseline` on an atomic inline: "Align the baseline of the box with
    // the baseline of the parent box. If the box does not have a baseline,
    // align the bottom margin edge with the parent's baseline": a 20px
    // image sits 20 above the baseline; the line is 20 + 2 high.
    let l = std("<div id=d>x<img id=i style='vertical-align:baseline;width:1px;height:20px'></div>");
    assert_eq!(baseline(&l), Some(px(20)), "{}", l.dump());
    assert_eq!((l.bb("d").height, l.bb("i").y), (px(22), 0));
    // A percentage: "Raise (positive value) or lower (negative value) the
    // box by this distance (a percentage of the 'line-height' value)". The
    // span's `line-height: normal` is A + D = 10px, so 50% is 5px.
    let l = std("<div id=d>x<span style='vertical-align:50%'>y</span></div>");
    let runs = l.runs("d");
    let base = runs.first().map_or(0, |r| r.2);
    assert_eq!(runs.get(1).map(|r| r.2), Some(base.saturating_sub(px(5))));
    let l = std("<div id=d>x<span style='vertical-align:-100%'>y</span></div>");
    let runs = l.runs("d");
    let base = runs.first().map_or(0, |r| r.2);
    assert_eq!(runs.get(1).map(|r| r.2), Some(base.saturating_add(px(10))));
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

// ---- Features with no test before: expected values derived by hand ----

/// The x of every glyph run of the element with `id`, in CSS px.
fn run_xs(l: &Laid, id: &str) -> Vec<i32> {
    l.runs(id).iter().map(|r| r.1.div_euclid(64)).collect()
}

/// The text of every glyph run of the element with `id`.
fn run_texts(l: &Laid, id: &str) -> Vec<String> {
    l.runs(id).into_iter().map(|r| r.0).collect()
}

/// CSS Text 3 §9.1 (`text-indent`), `each-line`: "Indentation affects the
/// first line of the block container as well as each line after a forced
/// line break, but does not affect lines after a soft wrap break." A 10px
/// em square font: "aaaa bbbb" at width 60 wraps after "aaaa" (indent 20 +
/// 40 = 60 fits; the next word does not).
#[test]
fn text_indent_each_line() {
    let l = std("<div id=d style='text-indent:20px each-line;width:60px'>aaaa bbbb<br>cc</div>");
    // Line 1 indented (first line); line 2 is after a soft wrap: not; line
    // 3 is after the forced break: indented.
    assert_eq!(run_xs(&l, "d"), [20, 0, 20], "{}", l.dump());
    // Without `each-line`, only the first line.
    let l = std("<div id=d style='text-indent:20px;width:60px'>aaaa bbbb<br>cc</div>");
    assert_eq!(run_xs(&l, "d"), [20, 0, 0], "{}", l.dump());
}

/// `hanging`: "Inverts which lines are affected." The first line is not
/// indented and every line after a soft wrap is; with `each-line` too, the
/// lines after forced breaks are the ones not indented.
#[test]
fn text_indent_hanging() {
    let l = std("<div id=d style='text-indent:20px hanging;width:60px'>aaaa bbbb cccc</div>");
    // Line 1 "aaaa" (0 + 40 of 60; "bbbb" does not fit), lines 2 and 3 are
    // after soft wraps: indented by 20, so 40 fit: "bbbb" then "cccc".
    assert_eq!(run_xs(&l, "d"), [0, 20, 20], "{}", l.dump());
    let l = std("<div id=d style='text-indent:20px each-line hanging;width:60px'>aaaa bbbb<br>cc</div>");
    // First line: not indented, so "aaaa bbbb" does not fit in 60 (90):
    // "aaaa" then, after a soft wrap, indented "bbbb"; after the forced
    // break, "cc" is not indented.
    assert_eq!(run_xs(&l, "d"), [0, 20, 0], "{}", l.dump());
}

/// §9.1: "<percentage>: Gives the amount of the indent as a percentage of
/// the block container's own content box inline size": 25% of 80 is 20; a
/// negative value moves the first line outwards.
#[test]
fn text_indent_percentage_and_negative() {
    let l = std("<div id=d style='text-indent:25%;width:80px'>a</div>");
    assert_eq!(run_xs(&l, "d"), [20], "{}", l.dump());
    let l = std("<div style='padding-left:30px'><div id=d style='text-indent:-10px'>a</div></div>");
    assert_eq!(run_xs(&l, "d"), [20], "{}", l.dump());
}

/// HTML §15.5.17 and §15.5.6: a `textarea` is `cols` characters wide
/// (`cols × average + (maximum − average)`: 10px each here, average equal to
/// maximum) and `rows` lines high (10px lines); the defaults are 20 and 2.
/// A checkbox, a radio button (HTML leaves their size to the user agent: 13
/// by 13, as the README lists) and buttons (the width of their label:
/// "Submit" and "Reset" by default, or the `value`).
#[test]
fn form_control_sizes() {
    let l = lay(
        &format!(
            "{STD}<div id=d><textarea id=t cols=5 rows=3></textarea><textarea id=u></textarea>\
             <input id=c type=checkbox><input id=r type=radio>\
             <input id=s type=submit><input id=x type=reset>\
             <input id=b type=button value=OK></div>"
        ),
        2000,
        600,
    );
    let size = |id: &str| (l.bb(id).width, l.bb(id).height);
    // 5 × 10 wide, 3 × 10 high.
    assert_eq!(size("t"), (px(50), px(30)), "{}", l.dump());
    // cols 20 × 10, rows 2 × 10.
    assert_eq!(size("u"), (px(200), px(20)));
    assert_eq!(size("c"), (px(13), px(13)));
    assert_eq!(size("r"), (px(13), px(13)));
    // "Submit" is six em squares, "Reset" five, "OK" two; one 10px line.
    assert_eq!(size("s"), (px(60), px(10)));
    assert_eq!(size("x"), (px(50), px(10)));
    assert_eq!(size("b"), (px(20), px(10)));
}

/// CSS Text 3 §3 (`white-space`): `nowrap` collapses white space like
/// `normal` but "wrap … no": "aa bb cc dd" stays on one line in a 50px box.
#[test]
fn white_space_nowrap() {
    let l = std("<div id=d style='width:50px;white-space:nowrap'>aa bb cc dd</div>");
    assert_eq!(l.lines("d").len(), 1, "{}", l.dump());
    assert_eq!(run_texts(&l, "d"), ["aa bb cc dd"]);
}

/// `pre-wrap`: "Preserve … wrap": a segment break is a forced break, runs of
/// spaces are kept, and lines wrap at soft wrap opportunities; "a sequence
/// of preserved spaces at the end of a line hangs" (does not wrap on its
/// own).
#[test]
fn white_space_pre_wrap() {
    // The newline is preserved: two lines even though both fit.
    let l = std("<div id=d style='white-space:pre-wrap'>a\nb</div>");
    assert_eq!(l.lines("d").len(), 2, "{}", l.dump());
    // Two spaces are two em squares: "a  b" is 40px wide.
    let l = std("<div id=d style='white-space:pre-wrap'>a  b</div>");
    assert_eq!(l.lines("d").len(), 1);
    assert_eq!(run_texts(&l, "d"), ["a  b"], "{}", l.dump());
    // At 30px "aa  bb": the spaces hang after "aa" (they are not counted
    // against the line's width) and "bb" starts the second line at x = 0.
    let l = std("<div id=d style='width:30px;white-space:pre-wrap'>aa  bb</div>");
    assert_eq!(l.lines("d").len(), 2, "{}", l.dump());
    assert_eq!(run_xs(&l, "d").last().copied(), Some(0));
    assert_eq!(run_texts(&l, "d").last().map(String::as_str), Some("bb"));
}

/// `break-spaces`: "like pre-wrap, except that preserved white space
/// sequences at the end of a line take up space and do not hang, and there
/// is a soft wrap opportunity after every preserved white space character".
/// At 30px, "aa" and one space fill line 1; the second space wraps, so line 2
/// is " " + " " + "b" = 30px.
#[test]
fn white_space_break_spaces() {
    let l = std("<div id=d style='width:30px;white-space:break-spaces'>aa   b</div>");
    assert_eq!(l.lines("d").len(), 2, "{}", l.dump());
    assert_eq!(run_texts(&l, "d"), ["aa ", "  b"], "{}", l.dump());
}

/// CSS Text 3 §5.5 (`overflow-wrap: break-word`): "An otherwise unbreakable
/// sequence of characters may be broken at an arbitrary point if there are
/// no otherwise-acceptable break points in the line": "abcdef" (60px) in a
/// 30px box is three characters per line. Without it, one overflowing line.
#[test]
fn overflow_wrap_break_word() {
    let l = std("<div id=d style='width:30px;overflow-wrap:break-word'>abcdef</div>");
    assert_eq!(run_texts(&l, "d"), ["abc", "def"], "{}", l.dump());
    let l = std("<div id=d style='width:30px'>abcdef</div>");
    assert_eq!(run_texts(&l, "d"), ["abcdef"]);
    // `anywhere` also counts for min-content: "soft wrap opportunities
    // introduced by `anywhere` are considered when calculating min-content
    // intrinsic sizes"; those of `break-word` are not. An inline block in a
    // 30px container is min(max(min-content, 30), max-content 60).
    let l = std("<div style='width:30px'><span id=s style='display:inline-block;overflow-wrap:anywhere'>abcdef</span></div>");
    assert_eq!(l.bb("s").width, px(30), "{}", l.dump());
    let l = std("<div style='width:30px'><span id=s style='display:inline-block;overflow-wrap:break-word'>abcdef</span></div>");
    assert_eq!(l.bb("s").width, px(60), "{}", l.dump());
}

/// CSS Text 3 §5.2 (`word-break: break-all`): "Breaking is allowed within
/// 'words'": "abcdef" in 30px breaks after three characters.
#[test]
fn word_break_break_all() {
    let l = std("<div id=d style='width:30px;word-break:break-all'>abcdef</div>");
    assert_eq!(run_texts(&l, "d"), ["abc", "def"], "{}", l.dump());
    let l = std("<div id=d style='width:30px;word-break:keep-all'>abcdef</div>");
    assert_eq!(run_texts(&l, "d"), ["abcdef"]);
}

/// The Quirks Mode Standard §3.3 and §3.4 apply in limited-quirks mode as
/// in quirks mode; §3.5 to §3.7 (percentage heights, filling the viewport)
/// do not. (`XHTML 1.0 Transitional`'s public identifier puts a document in
/// limited-quirks mode: HTML §13.2.6.4.1.)
#[test]
fn limited_quirks_mode() {
    let head = "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \
        \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">\
        <style>html { font-size: 10px } body { margin: 0 }</style>";
    let limited = |body: &str| lay(&format!("{head}{body}"), 200, 100);
    // §3.3: a span without text and borders has a line-height of zero; the
    // line with a 1px image is 1px high (no-quirks: 10, the strut).
    let doc = "<div id=d><span><img style='width:1px;height:1px'></span></div>";
    assert_eq!(limited(doc).bb("d").height, px(1));
    // §3.4: blocks ignore the strut: 10px in an element of font-size 20.
    let doc = "<div id=d style='font-size:20px'><span style='font-size:10px'>x</span></div>";
    assert_eq!(limited(doc).bb("d").height, px(10));
    // §3.5: no percentage-height lookup past an `auto` ancestor: computes to
    // auto, so 0 (quirks mode: 50).
    let l = limited("<div id=d style='height:50%'></div>");
    assert_eq!(l.bb("d").height, 0, "{}", l.dump());
    // §3.6, §3.7: the `body` is not stretched: 10px, not 84.
    let l = limited("<body id=b style='margin:8px'><div style='height:10px'></div>");
    assert_eq!(l.bb("b").height, px(10), "{}", l.dump());
}

/// CSS 2.1 §8.3: "<percentage>: The percentage is calculated with respect to
/// the width of the generated box's containing block. Note that this is true
/// for 'margin-top' and 'margin-bottom' as well"; §8.4 says the same of
/// padding. In a 100px containing block, `margin: 10% 20%` is 10px above and
/// below and 20px at the sides, and `padding: 5%` is 5px all round.
#[test]
fn percentage_margins_and_padding() {
    let l = std("<div style='width:100px'><div id=c style='margin:10% 20%;padding:5%;height:1px'></div></div>");
    let f = l.frag("c");
    assert_eq!(f.margin.top, px(10), "{}", l.dump());
    assert_eq!(f.margin.bottom, px(10));
    assert_eq!((f.margin.left, f.margin.right), (px(20), px(20)));
    assert_eq!(
        (f.padding.top, f.padding.right, f.padding.bottom, f.padding.left),
        (px(5), px(5), px(5), px(5))
    );
    // §10.3.3: width auto = 100 − 20 − 20 (margins) = 60 border box; the
    // height 1 plus padding 5 + 5 = 11; the top margin collapses through
    // the parent (§8.3.1), so the box is at y = 10.
    assert_eq!(f.border_box, rect(20, 10, 60, 11));
}

/// CSS 2.1 §9.4.2: an inline box "is split into several boxes and these boxes
/// are distributed across several line boxes"; "margins, borders, and padding
/// have no visual effect where the split occurs". A bordered, padded span
/// across two lines has its start edge (2px border + 3px padding) on line 1
/// only, so line 1's text starts at 5 and line 2's at 0, and its end edge on
/// line 2 only.
#[test]
fn split_inline_with_borders() {
    let l = std(
        "<div id=d style='width:50px'><span style='border:2px solid;padding:0 3px'>aaa bbb</span></div>",
    );
    assert_eq!(l.lines("d").len(), 2, "{}", l.dump());
    assert_eq!(run_xs(&l, "d"), [5, 0]);
    let pieces: Vec<(bool, bool)> = l
        .lines("d")
        .iter()
        .flat_map(|line| line.items.iter())
        .filter_map(|i| match i {
            LineItem::Inline(p) => Some((p.start_edge, p.end_edge)),
            _ => None,
        })
        .collect();
    assert_eq!(pieces, [(true, false), (false, true)]);
}

/// CSS 2.1 §11.1.1: "UAs must apply the 'overflow' property set on the root
/// element to the viewport. When the root element is an 'HTML' element …
/// and its 'overflow' is 'visible' … user agents must instead apply the
/// 'overflow' from the first such child element to the viewport. The element
/// from which the value is propagated must have a used value for 'overflow'
/// of 'visible'." So a `body` with `overflow: hidden` under a `visible` root
/// is not a block formatting context root: its first child's top margin
/// collapses through it (§8.3.1), putting the `body` at y = 20. If the root
/// has its own non-`visible` `overflow`, the `body`'s is not propagated and
/// the `body` does establish one: it stays at y = 0 with the margin inside.
#[test]
fn overflow_propagates_from_body_to_the_viewport() {
    let doc = |html_style: &str| {
        lay(
            &format!(
                "<!DOCTYPE html><style>html {{ font-size: 10px;{html_style} }} body {{ margin: 0 }}</style>\
                 <body id=b style='overflow:hidden'><div id=c style='margin-top:20px;height:5px'></div>"
            ),
            200,
            100,
        )
    };
    let l = doc("");
    assert_eq!((l.bb("b").y, l.bb("c").y), (px(20), px(20)), "{}", l.dump());
    let l = doc("overflow:hidden");
    assert_eq!((l.bb("b").y, l.bb("c").y), (0, px(20)), "{}", l.dump());
    // The body's height then holds the child's margin (§10.6.7).
    assert_eq!(l.bb("b").height, px(25));
}

/// `ol` markers through layout: the decimal counter style's marker is the
/// ordinal and ". " (CSS Counter Styles 3 §6.1: suffix ". "), placed in the
/// margin, ending at the content edge of the list item (§12.5: `outside`).
/// `value=10` sets the counter (HTML §4.4.8), so "10. " is four em squares.
#[test]
fn ol_markers_through_layout() {
    let l = std(
        "<ol style='padding-left:50px'><li id=a style='list-style-type:decimal'>x\
         <li id=b style='list-style-type:decimal'>y\
         <li id=c value=10 style='list-style-type:decimal'>z</ol>",
    );
    let marker = |id: &str| {
        l.tree
            .children(l.id(id))
            .first()
            .and_then(|&m| l.frags.fragment(m))
            .map(|f| f.border_box)
    };
    // "1. " and "2. " are three em squares ending at the content edge, 50.
    assert_eq!(marker("a"), Some(rect(20, 0, 30, 10)), "{}", l.dump());
    assert_eq!(marker("b"), Some(rect(20, 10, 30, 10)));
    // "10. " is four.
    assert_eq!(marker("c"), Some(rect(10, 20, 40, 10)));
}

// ---- Markers, the table placeholder, depth ----

/// A list item's marker ends at its content edge, on its first baseline.
#[test]
fn markers_sit_outside() {
    let l = std("<ul style='padding-left:40px'><li id=l>ab</li></ul>");
    let li = l.id("l");
    let marker = l
        .tree
        .children(li)
        .first()
        .and_then(|&m| l.frags.fragment(m))
        .map(|f| f.border_box);
    // The marker "• " is two em squares, ending at the content edge (40).
    assert_eq!(marker, Some(rect(20, 0, 20, 10)), "{}", l.dump());
}

/// The table placeholder (`mod.rs`): rows and cells as blocks, one below
/// the other.
#[test]
fn table_placeholder_stacks_cells() {
    let l = std("<table><tr><td id=a>a</td><td id=b>b</td></tr></table>");
    assert_eq!(l.bb("a").y, 0, "{}", l.dump());
    assert_eq!(l.bb("b").y, px(10));
}

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

// ---- Depth: other shapes than plain blocks ----

/// The text run of a document with the text "x" (units after Phase I), to
/// put into hand-built box trees (the units are made by `boxes::build`).
fn x_run() -> TextRun {
    let l = std("<p>x</p>");
    let found = l.tree.boxes.iter().find_map(|b| match &b.kind {
        BoxKind::Text(run) => Some(run.clone()),
        _ => None,
    });
    assert!(found.is_some(), "the document has a text run");
    found.unwrap_or(TextRun {
        text: "x".to_owned(),
        style: TextStyle::INITIAL,
        units: Vec::new(),
    })
}

/// How deep: far past a recursive implementation's stack (100,000), less
/// under Miri, where every box costs far more.
fn deep(native: usize) -> usize {
    if cfg!(miri) { 200 } else { native }
}

/// Lays out `tree` (every style initial: the boxes have no nodes) and
/// returns what must not depend on how deeply the content is nested: the
/// outermost block's border box, and the text runs (x, baseline), with the
/// time layout took.
fn laid_signature(tree: &BoxTree) -> (Option<Rect>, Vec<(i32, i32)>, std::time::Duration) {
    struct NoStyle;
    impl StyleFns for NoStyle {
        fn style(&self, _node: usize) -> Option<&ComputedStyle> {
            None
        }
    }
    let arena = Arena::new(Vec::new());
    let start = std::time::Instant::now();
    let f = layout(tree, &arena, &NoStyle, &BoxFont, Viewport::px(800, 600));
    let took = start.elapsed();
    let runs = f
        .lines
        .iter()
        .flat_map(|l| l.items.iter())
        .filter_map(|i| match i {
            LineItem::Text(r) => Some((r.x, r.baseline)),
            _ => None,
        })
        .collect();
    // Box 1 is the first child of the root in every tree below.
    (f.fragment(1).map(|b| b.border_box), runs, took)
}

/// The depth-`n` tree of `shape` and its signature.
fn signature_of(shape: &str, n: usize) -> (Option<Rect>, Vec<(i32, i32)>, std::time::Duration) {
    let mut t = BoxTree::new();
    let mut p = t.add_child(BoxTree::ROOT, BoxKind::Block, None);
    match shape {
        // `<span><span>…x…</span></span>`: one inline formatting context.
        "inline" => {
            for _ in 0..n {
                p = t.add_child(p, BoxKind::Inline(Fragment::WHOLE), None);
            }
        }
        // Each inline block holds the next in its own line.
        "inline-block" => {
            for _ in 0..n {
                p = t.add_child(p, BoxKind::InlineBlock, None);
            }
        }
        // `<span><div>…</div></span>` n times, as `boxes::build` splits it
        // (CSS 2.1 §9.2.1.1): an anonymous block with the first fragment,
        // the div, an anonymous block with the last.
        "split" => {
            for _ in 0..n {
                let a = t.add_child(p, BoxKind::Block, None);
                t.add_child(
                    a,
                    BoxKind::Inline(Fragment {
                        first: true,
                        last: false,
                    }),
                    None,
                );
                let d = t.add_child(p, BoxKind::Block, None);
                let c = t.add_child(p, BoxKind::Block, None);
                t.add_child(
                    c,
                    BoxKind::Inline(Fragment {
                        first: false,
                        last: true,
                    }),
                    None,
                );
                p = d;
            }
        }
        // `<table><tr><td>` n times.
        _ => {
            for _ in 0..n {
                let w = t.add_child(p, BoxKind::TableWrapper { inline: false }, None);
                let table = t.add_child(w, BoxKind::Table { inline: false }, None);
                let group = t.add_child(table, BoxKind::RowGroup(RowGroup::Body), None);
                let row = t.add_child(group, BoxKind::Row, None);
                p = t.add_child(row, BoxKind::Cell, None);
            }
        }
    }
    t.add_child(p, BoxKind::Text(x_run()), None);
    laid_signature(&t)
}

/// No recursion in the inline formatting context, inline blocks, split
/// inlines and the table placeholder: each shape nested far deeper than a
/// recursive implementation's stack lays out, and (nothing in them has
/// edges, margins or size) gives exactly what one level gives: the same
/// outermost block, the same text run at the same place (CSS 2.1 §9.4.2:
/// an inline box without edges does not move its content; §10.6.3 and
/// §10.6.7: the heights are the content's). The time is printed, to see
/// growth: each shape was measured at several depths while writing this
/// (layout alone is linear in the number of boxes; parsing and the cascade
/// of such documents are not, which is why the trees are built by hand:
/// measured in a debug build from 500 to 4,000 nested levels, each doubling
/// took layout 2x, but the parser about 4x for the inline shapes and the
/// cascade about 4x for the block-in-inline and table shapes).
#[test]
fn deep_shapes_lay_out_without_recursion_and_unchanged() {
    for (shape, native) in [
        ("inline", 100_000),
        ("inline-block", 100_000),
        ("split", 50_000),
        ("table", 40_000),
    ] {
        let n = deep(native);
        let (outer, runs, took) = signature_of(shape, n);
        let (outer1, runs1, _) = signature_of(shape, 1);
        eprintln!("deep {shape} depth {n}: layout took {took:?}");
        assert!(outer.is_some(), "{shape}: the outer block has a fragment");
        assert_eq!(runs.len(), 1, "{shape}: one text run");
        assert_eq!(runs, runs1, "{shape}: the text is where depth 1 puts it");
        assert_eq!(outer, outer1, "{shape}: the outer block is as at depth 1");
    }
}

// ---- Extremes ----

/// Lengths far past any real page, and past `i32` in 1/64 px (a pixel is 64
/// units, so `i32::MAX` is 33,554,431 px), go through the whole pipeline.
#[test]
fn extreme_lengths_saturate_and_never_panic() {
    let l = lay(
        &format!(
            "{STD}<div id=a style='width:99999999px;height:99999999px'></div>\
             <div id=b style='margin:-99999999px 0 0 -99999999px;height:10px'></div>\
             <div id=c style='padding:99999999px;margin:99999999px;border:99999999px solid'>x</div>\
             <div id=d style='font-size:99999999px'>x y</div>\
             <div id=e style='width:2147483647px;margin-left:2147483647px;height:2147483647px'></div>\
             <div id=f style='line-height:99999999px;text-indent:-99999999px'>x</div>\
             <div id=g style='width:-5px;height:-5px;margin:-2147483648px'>x</div>\
             <div><span id=h style='display:inline-block;width:99999999px'>y</span><img id=i style='width:99999999px;height:99999999px'></div>"
        ),
        200,
        100,
    );
    let dump = l.dump();
    // No fragment has a negative size or an edge that wrapped around.
    for f in l.frags.boxes.iter().flatten() {
        let r = f.border_box;
        assert!(r.width >= 0 && r.height >= 0, "negative size: {dump}");
        assert!(r.right() >= r.x && r.bottom() >= r.y, "wrapped: {dump}");
    }
    for line in &l.frags.lines {
        assert!(line.rect.width >= 0 && line.rect.height >= 0, "{dump}");
    }
    // A length beyond what the style crate keeps is clamped to the same
    // value however far beyond: 99,999,999px and 2,147,483,647px give the
    // same used width and height.
    let (a, e) = (l.frag("a"), l.frag("e"));
    assert_eq!(a.border_box.width, e.border_box.width, "{dump}");
    assert_eq!(a.border_box.height, e.border_box.height, "{dump}");
    assert!(a.border_box.width > px(10_000_000), "{dump}");
    // CSS 2.1 §10.3.3 for an `auto` width: the margins, borders, padding and
    // width add up to the containing block's 200px, as long as nothing
    // saturated: `b`'s margin-left is minus the clamp and its width 200px
    // more.
    let b = l.frag("b");
    assert!(b.margin.left < px(-10_000_000), "{dump}");
    assert_eq!(
        b.margin.left
            .saturating_add(b.border_box.width)
            .saturating_add(b.margin.right),
        px(200),
        "{dump}"
    );
    // A margin of i32::MIN px is clamped like -99,999,999px, on every side.
    let g = l.frag("g");
    assert_eq!(
        (g.margin.top, g.margin.right, g.margin.bottom, g.margin.left),
        (b.margin.left, b.margin.left, b.margin.left, b.margin.left),
        "{dump}"
    );
    // `c`'s border box, padding and borders, each at the clamp, sum past
    // `i32::MAX` and stop there; its text is as far right.
    let c = l.frag("c");
    assert_eq!(c.border_box.width, i32::MAX, "{dump}");
    assert_eq!(c.border_box.height, i32::MAX, "{dump}");
    // Boxes in flow with non-negative margins below one another do not
    // move up: a, c, d, e in order (§9.4.1).
    let ys: Vec<i32> = ["a", "c", "d", "e"].iter().map(|i| l.bb(i).y).collect();
    assert!(ys.windows(2).all(|w| w.first() <= w.get(1)), "{ys:?} {dump}");
    // A huge `font-size` gives lines as high as the (clamped) font: `d`'s
    // two lines are each as high as one, and its height is their sum.
    let d = l.lines("d");
    assert_eq!(d.len(), 2, "{dump}");
    let line_height = d.first().map(|x| x.rect.height);
    assert!(line_height > Some(px(10_000_000)), "{dump}");
    assert_eq!(
        Some(l.bb("d").height),
        line_height.map(|h| h.saturating_mul(2)),
        "{dump}"
    );
    // A negative `text-indent` moves the first line left of the box.
    assert!(l.runs("f").first().is_some_and(|r| r.1 < 0), "{dump}");
}
