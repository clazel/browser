//! The cascade end to end: documents parsed by `clazel-treebuilder`, their sources collected
//! by `sources::collect`, cascaded.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use super::computed::*;
use super::*;
use crate::sources::collect;
use crate::values::number::Num;
use clazel_dom::spec::DocumentMode;

/// No encodings: every test document is already code points.
pub struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// `html` parsed as a document.
pub fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let url: Vec<u32> = "http://example.com/".chars().map(u32::from).collect();
    parse_real(&NoEncodings, &input, url, false, false).0.arena
}

/// The element whose `id` is `id`.
pub fn by_id(arena: &Arena, id: &str) -> Option<usize> {
    (0..arena.len()).find(|&n| match arena.kind(n) {
        ExecKind::Element { attributes, .. } => hints::attribute(attributes, "id")
            .is_some_and(|v| v.iter().copied().eq(id.chars().map(u32::from))),
        _ => false,
    })
}

/// The table of `arena`'s document in an 800 by 600 viewport. Under Miri, the user agent
/// sheets are cut to the rules that can match the document ([`ua::Sheets::for_document`]):
/// preparing and matching the whole sheets takes minutes per document there.
/// `filtered_sheets_give_the_same_tables` checks natively that both give the same table.
fn table_of(arena: &Arena) -> ComputedTable {
    let sources = collect(arena);
    let device = Device::screen(800, 600);
    if cfg!(miri) {
        cascade_with(&ua::sheets().for_document(arena), arena, &sources, device)
    } else {
        cascade(arena, &sources, device)
    }
}

/// A document, parsed and cascaded once.
struct Doc {
    arena: Arena,
    table: ComputedTable,
}

impl Doc {
    fn new(html: &str) -> Doc {
        let arena = parse(html);
        let table = table_of(&arena);
        Doc { arena, table }
    }

    /// The style of the element `id`.
    fn style(&self, id: &str) -> ComputedStyle {
        by_id(&self.arena, id)
            .and_then(|n| self.table.get(n).cloned())
            .unwrap_or_else(ComputedStyle::initial)
    }
}

const UA_DOC: &str = "<!DOCTYPE html><body id=b><h1 id=h>x</h1><p id=p>y</p><ul id=u><li id=l>z</ul>\
               <div id=d hidden></div><b id=bold>b</b><a id=a href=x>a</a>\
               <table id=t><tr><th id=th>h</th></tr></table><pre id=pre>p</pre>";

const AUTHOR_DOC: &str = "<!DOCTYPE html><style>#x { color: red } .c { color: green !important } \
               p { color: blue; width: 10px } img { width: 30px }</style>\
               <p id=x class=c style='color: black'>a</p>\
               <p id=y style='color: rgb(1, 2, 3); width: 5px'>b</p>\
               <img id=i width=200 height=20><img id=j width=200 style='width: 7px'>\
               <table id=t width=50% bgcolor=red style='background-color: green'></table>";

const INHERIT_DOC: &str = "<!DOCTYPE html><style>\
               #o { color: green; background: red; font-size: 20px; line-height: 1.5 }\
               #i { color: red; background-color: red; font-size: 2em; }\
               #i { color: unset; background-color: unset; border: 2px solid; }\
               #k { color: initial; font-size: inherit; display: revert; }\
               #r { display: inline; display: revert; margin: revert; }\
               </style><div id=o><div id=i><span id=k>x</span></div><p id=r>y</p></div>";

const QUIRKS_DOC: &str = "<style>body { font-size: 20px; color: f00 } td { width: 10 }</style>\
               <body><table id=t><tr><td id=d><p id=p>x</p></td></tr></table>\
               <p id=q>y</p></body>";

const HN_DOC: &str = "<html lang=en op=news><head><style>\
               body { font-family: Verdana, Geneva, sans-serif; font-size: 10pt; color: #828282 }\
               td { font-family: Verdana, Geneva, sans-serif; font-size: 10pt; color: #828282 }\
               .pagetop { font-size: 10pt; color: #222222 }\
               a:link { color: #000000; text-decoration: none }\
               @media only screen and (min-width: 300px) and (max-width: 750px) { .c { width: 1px } }\
               </style></head><body><center>\
               <table id=hnmain border=0 cellpadding=0 cellspacing=0 width=85% bgcolor=#f6f6ef>\
               <tr><td id=top bgcolor=#ff6600><span class=pagetop id=pt><a id=link href=news>Hacker News</a></span></td></tr>\
               <tr style='height:10px' id=spacer></tr>\
               <tr><td id=ind><img id=s src=s.gif height=1 width=40></td>\
               <td valign=top class=votelinks id=v><center>x</center></td></tr>\
               </table></center></body></html>";

fn px(v: i32) -> i32 {
    v.saturating_mul(64)
}

fn lp_px(v: i32) -> Size {
    Size::Lp(Lp::Px64(px(v)))
}

#[test]
fn user_agent_sheet() {
    let doc = Doc::new(UA_DOC);
    let s = |id| doc.style(id);
    let b = s("b");
    assert_eq!(b.display, Display::Block);
    assert_eq!(b.margin, [lp_px(8); 4], "body's 8px margins");
    let h = s("h");
    assert_eq!(h.font_size, px(32));
    assert_eq!(h.font_weight, Num::from_int(700));
    // 0.67em of 32px: 21.44px.
    assert_eq!(h.margin[0], Size::Lp(Lp::Px64(1372)));
    assert_eq!(h.margin[1], Size::Lp(Lp::Px64(0)));
    let p = s("p");
    assert_eq!(
        (p.display, p.margin[0], p.margin[2]),
        (Display::Block, lp_px(16), lp_px(16))
    );
    let u = s("u");
    assert_eq!(u.padding[3], Lp::Px64(px(40)));
    assert_eq!(u.list_style_type, ListStyleType::Named("disc"));
    let l = s("l");
    assert_eq!(l.display, Display::ListItem);
    assert_eq!(l.text_align, TextAlign::Left, "match-parent from start");
    assert_eq!(s("d").display, Display::None);
    assert_eq!(s("bold").font_weight, Num::from_int(700));
    let a = s("a");
    assert_eq!(a.color, [0, 0, 0xEE, 255]);
    assert!(a.text_decoration_line.underline);
    let t = s("t");
    assert_eq!(
        (t.display, t.border_spacing),
        (Display::Table, [px(2), px(2)])
    );
    let th = s("th");
    assert_eq!(
        (th.display, th.text_align),
        (Display::TableCell, TextAlign::Center)
    );
    assert_eq!(th.padding, [Lp::Px64(px(1)); 4]);
    assert_eq!(
        th.vertical_align,
        VerticalAlign::Middle,
        "inherited from the row group"
    );
    let pre = s("pre");
    assert_eq!(pre.white_space, WhiteSpace::Pre);
    assert_eq!(pre.font_family, 1);
}

#[test]
fn author_rules_hints_and_style_attributes() {
    let doc = Doc::new(AUTHOR_DOC);
    assert_eq!(
        doc.style("x").color,
        [0, 128, 0, 255],
        "important beats the attribute"
    );
    let y = doc.style("y");
    assert_eq!((y.color, y.width), ([1, 2, 3, 255], lp_px(5)));
    let i = doc.style("i");
    assert_eq!(
        (i.width, i.height),
        (lp_px(30), lp_px(20)),
        "an author rule beats a hint"
    );
    assert_eq!(doc.style("j").width, lp_px(7));
    let t = doc.style("t");
    assert_eq!(
        t.width,
        Size::Lp(Lp::Percent(Num {
            millionths: 50_000_000,
            is_integer: false
        }))
    );
    assert_eq!(t.background_color, [0, 128, 0, 255]);
}

#[test]
fn inheritance_and_keywords() {
    let doc = Doc::new(INHERIT_DOC);
    let i = doc.style("i");
    assert_eq!(i.color, [0, 128, 0, 255], "unset inherits color");
    assert_eq!(
        i.background_color, TRANSPARENT,
        "unset resets background-color"
    );
    assert_eq!(i.font_size, px(40));
    assert_eq!(
        i.line_height,
        LineHeight::Number(Num {
            millionths: 1_500_000,
            is_integer: false
        })
    );
    assert_eq!(i.border_color, [[0, 128, 0, 255]; 4], "currentcolor");
    let k = doc.style("k");
    assert_eq!(k.color, BLACK);
    assert_eq!(k.font_size, px(40));
    assert_eq!(
        k.display,
        Display::Inline,
        "revert reaches the UA's (no) rule for span"
    );
    let r = doc.style("r");
    assert_eq!(r.display, Display::Block, "revert reaches p's UA rule");
    assert_eq!(r.margin[0], lp_px(20), "1em of the inherited 20px");
}

#[test]
fn quirks_mode() {
    // No doctype: quirks mode. Tables reset the font size and the hashless colour and
    // unitless length quirks apply to author sheets.
    let doc = Doc::new(QUIRKS_DOC);
    let t = doc.style("t");
    assert_eq!(
        t.font_size,
        px(16),
        "tables do not inherit font-size in quirks mode"
    );
    assert_eq!(t.color, [255, 0, 0, 255]);
    assert_eq!(doc.style("d").width, lp_px(10));
    let p = doc.style("p");
    assert_eq!(
        (p.margin[0], p.margin[2]),
        (lp_px(0), lp_px(0)),
        "margin collapsing quirks"
    );
    let q = doc.style("q");
    assert_eq!(q.margin[0], lp_px(20), "not first in body: 1em of 20px");
}

#[test]
fn hacker_news_shape() {
    let doc = Doc::new(HN_DOC);
    let t = doc.style("hnmain");
    assert_eq!(t.background_color, [0xf6, 0xf6, 0xef, 255]);
    assert_eq!(t.border_spacing, [0, 0]);
    assert_eq!(t.font_size, px(16), "quirks: table resets font-size");
    let top = doc.style("top");
    assert_eq!(top.background_color, [0xff, 0x66, 0x00, 255]);
    assert_eq!(top.padding, [Lp::Px64(0); 4], "cellpadding");
    assert_eq!(top.font_size, 853, "10pt is 13.33px");
    let pt = doc.style("pt");
    assert_eq!(pt.color, [0x22, 0x22, 0x22, 255]);
    let link = doc.style("link");
    assert_eq!(link.color, BLACK);
    assert!(!link.text_decoration_line.underline);
    assert_eq!(doc.style("spacer").height, lp_px(10));
    let s = doc.style("s");
    assert_eq!((s.width, s.height), (lp_px(40), lp_px(1)));
    assert_eq!(doc.style("v").vertical_align, VerticalAlign::Top);
    let (arena, table) = (&doc.arena, &doc.table);
    let center = (0..arena.len()).find(|&n| hints::is_html(arena, n, "center"));
    let c = center.and_then(|n| table.get(n));
    assert_eq!(
        c.map(|c| c.align_descendants),
        Some(Some(AlignDescendants::Center))
    );
    let families: Vec<String> = table
        .family(
            table
                .get(by_id(arena, "top").unwrap_or(0))
                .unwrap_or(&ComputedStyle::initial()),
        )
        .iter()
        .map(|f| match f {
            Family::Name(n) => n.iter().filter_map(|&c| char::from_u32(c)).collect(),
            Family::Generic(g) => (*g).to_owned(),
        })
        .collect();
    assert_eq!(families, vec!["Verdana", "Geneva", "sans-serif"]);
}

#[test]
fn tree_order_visits_each_node_once() {
    let arena = parse("<!DOCTYPE html><p>a<b>c</b></p><!-- x --><div></div>");
    let order = tree_order(&arena);
    let mut sorted = order.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), order.len());
    assert_eq!(order.first(), Some(&0));
    // Parents come before their children.
    for (i, &n) in order.iter().enumerate() {
        if let Some(p) = arena.parent(n) {
            assert!(order.iter().position(|&m| m == p).is_some_and(|j| j < i));
        }
    }
}

/// The sheets cut to a document's rules give the same table as the whole sheets, for every
/// document of these tests (the cut is what the tests run under Miri).
#[test]
#[cfg_attr(
    miri,
    ignore = "cascades with the whole user agent sheets, which take minutes per document under \
              Miri; the comparison is the same natively"
)]
fn filtered_sheets_give_the_same_tables() {
    for doc in [UA_DOC, AUTHOR_DOC, INHERIT_DOC, QUIRKS_DOC, HN_DOC] {
        let arena = parse(doc);
        let sources = collect(&arena);
        let device = Device::screen(800, 600);
        let small = ua::sheets().for_document(&arena);
        assert!(small.ua.rules.len() < ua::sheets().ua.rules.len());
        assert_eq!(
            cascade_with(&small, &arena, &sources, device),
            cascade(&arena, &sources, device),
            "{doc}"
        );
    }
}

// The cascade through parsed documents and style sheets. Each expectation is derived from
// CSS Cascade 4's sorting order (§6.1: "Origin and Importance", "Specificity", "Order of
// Appearance") and from the sections cited at the test, not from the code's output.

const RED: [u8; 4] = [255, 0, 0, 255];
const GREEN: [u8; 4] = [0, 128, 0, 255];
const BLUE: [u8; 4] = [0, 0, 255, 255];

/// The computed `color` of the element `id` of `html`.
fn color_of(html: &str, id: &str) -> [u8; 4] {
    Doc::new(html).style(id).color
}

/// CSS Cascade 4 §6.1 "Specificity": the declaration of the selector with the highest
/// specificity wins, before "Order of Appearance". An id beats a class beats a type, wherever
/// the rules stand in the sheet.
#[test]
fn author_specificity_beats_order() {
    let rules = [
        "#a { color: red }",
        ".a { color: green }",
        "p { color: blue }",
    ];
    for order in [[0, 1, 2], [2, 1, 0], [1, 2, 0], [1, 0, 2]] {
        let css: String = order
            .iter()
            .filter_map(|&i| rules.get(i))
            .copied()
            .collect();
        let html = format!("<!DOCTYPE html><style>{css}</style><p id=a class=a>x</p>");
        assert_eq!(color_of(&html, "a"), RED, "{css}");
    }
    let html = "<!DOCTYPE html><style>p { color: blue } .a { color: green }</style>\
                <p id=a class=a>x</p>";
    assert_eq!(color_of(html, "a"), GREEN);
    // (1,0,0) beats (0,2,0), although it comes first.
    let html = "<!DOCTYPE html><style>#a { color: red } .a.b { color: green }</style>\
                <p id=a class='a b'>x</p>";
    assert_eq!(color_of(html, "a"), RED);
}

/// §6.1 "Order of Appearance: ... the last declaration in document order wins", within one
/// sheet, and across sheets in tree order (CSSOM §6.2: style sheets are ordered by their
/// owner nodes' tree order): a rule of a later `<style>` beats an equal-specificity rule of an
/// earlier one, whatever their positions in their sheets.
#[test]
fn order_of_appearance_within_and_across_sheets() {
    let one = "<!DOCTYPE html><style>.c { color: red } .c { color: green }</style><p class=c id=a>";
    assert_eq!(color_of(one, "a"), GREEN);
    let two = "<!DOCTYPE html><style>.c { color: red } .c { color: green }</style>\
               <style>.c { color: blue }</style><p class=c id=a>";
    assert_eq!(color_of(two, "a"), BLUE);
    let three = "<!DOCTYPE html><style>p { color: red } .c { color: green }</style>\
                 <style>.c { color: blue } p { color: red }</style><p class=c id=a>";
    assert_eq!(
        color_of(three, "a"),
        BLUE,
        ".c (0,1,0) beats p (0,0,1) in both sheets, and the later sheet's .c is last"
    );
    // A `<style>` in the body counts by tree order too.
    let body = "<!DOCTYPE html><style>.c { color: red }</style><p class=c id=a>x</p>\
                <style>.c { color: green }</style><p class=c id=b>y</p>";
    let doc = Doc::new(body);
    assert_eq!(doc.style("a").color, GREEN);
    assert_eq!(doc.style("b").color, GREEN);
}

/// §6.2 and §6.1: "Important user agent declarations" beat all author declarations, normal
/// and important. The user agent sheet (HTML §15.5.2) has `input[type=hidden i] { display:
/// none !important }`, which the author's `display` cannot change.
#[test]
fn user_agent_important_beats_author_normal_and_important() {
    let html = "<!DOCTYPE html><style>input { display: inline-block }\
                #n { display: inline-block !important }</style>\
                <input type=hidden id=h><input type=hidden id=n style='display: block !important'>\
                <input type=text id=t>";
    let doc = Doc::new(html);
    assert_eq!(
        doc.style("h").display,
        Display::None,
        "against author normal"
    );
    assert_eq!(
        doc.style("n").display,
        Display::None,
        "against author important"
    );
    assert_eq!(
        doc.style("t").display,
        Display::InlineBlock,
        "a text input has no important rule: the author's normal one applies"
    );
}

/// §6.1: important author declarations beat normal ones; a `style` attribute beats selectors
/// at the same importance (CSS Style Attributes §4: "a specificity higher than any
/// selector"), and its !important beats an important sheet rule.
#[test]
fn style_attribute_and_importance() {
    let html = "<!DOCTYPE html><style>\
                #a { color: red !important } #b { color: red !important } #c { color: red }\
                #d { color: red !important }</style>\
                <p id=a style='color: green'>1</p>\
                <p id=b style='color: green !important'>2</p>\
                <p id=c style='color: green'>3</p>\
                <p id=d style='color: green !important; color: blue !important'>4</p>";
    let doc = Doc::new(html);
    assert_eq!(
        doc.style("a").color,
        RED,
        "important rule beats a normal attribute"
    );
    assert_eq!(
        doc.style("b").color,
        GREEN,
        "important attribute beats an important rule"
    );
    assert_eq!(
        doc.style("c").color,
        GREEN,
        "normal attribute beats a normal rule"
    );
    assert_eq!(
        doc.style("d").color,
        BLUE,
        "the last important attribute declaration"
    );
}

/// CSS Cascade 5 §7.3.5 `revert-layer`, with no `@layer` rules: the author origin is one
/// layer, so rolling back from it reaches the user agent origin ("the layer below"). For `p`
/// the UA has `display: block`, so an author `display: revert-layer` after `display: inline`
/// computes block; for `span`, to which the UA gives no `display`, the initial `inline`.
#[test]
fn revert_layer_rolls_back_the_author_origin() {
    let html = "<!DOCTYPE html><style>p { display: inline } p { display: revert-layer }\
                span { display: block } span { display: revert-layer }\
                #q { display: inline-block } </style>\
                <p id=p>x</p><span id=s>y</span><p id=q>z</p>";
    let doc = Doc::new(html);
    assert_eq!(doc.style("p").display, Display::Block);
    assert_eq!(doc.style("s").display, Display::Inline);
    assert_eq!(
        doc.style("q").display,
        Display::InlineBlock,
        "no revert-layer: the id wins"
    );
}

/// Media Queries 4 §2 (and HTML §4.2.6): rules in an `@media` block apply exactly when the
/// query matches. At 800 by 600 `(min-width: 700px)` matches and `(max-width: 100px)` does
/// not; a `media` attribute on the `<style>` gates the whole sheet the same way.
#[test]
fn media_gated_rules() {
    let html = "<!DOCTYPE html><style>.c { color: red }\
                @media (min-width: 700px) { .c { color: green } }\
                @media (max-width: 100px) { .c { color: blue } }</style>\
                <style media='(max-width: 100px)'>#a { color: blue }</style>\
                <style media='(min-width: 700px)'>#b { width: 77px }</style>\
                <p id=a class=c>x</p><p id=b class=c>y</p>";
    let doc = Doc::new(html);
    assert_eq!(
        doc.style("a").color,
        GREEN,
        "the matching block applies; the others do not"
    );
    assert_eq!(doc.style("b").width, lp_px(77));
    // Rule order still decides: here the matching block comes before `.c { red }`.
    let early = "<!DOCTYPE html><style>@media (min-width: 700px) { .c { color: green } }\
                 .c { color: red }</style><p id=a class=c>x</p>";
    assert_eq!(color_of(early, "a"), RED);
}

/// A shorthand is its longhands (CSS Cascade 4 §3.3 "Shorthand Properties": it "is
/// equivalent to ... all its longhand sub-properties"), each competing in the cascade by its
/// own declaration's order: a later longhand beats an earlier shorthand's, and the reverse.
#[test]
fn shorthand_and_longhand_order() {
    let html = "<!DOCTYPE html><style>\
                #a { margin: 10px; margin-top: 5px }\
                #b { margin-top: 5px; margin: 10px }\
                #c { margin: 10px } #c { margin-left: 3px }\
                #d { margin-left: 3px } #d { margin: 10px }\
                #e { margin-left: 3px !important } #e { margin: 10px }</style>\
                <div id=a></div><div id=b></div><div id=c></div><div id=d></div><div id=e></div>";
    let doc = Doc::new(html);
    let m = |id| doc.style(id).margin;
    assert_eq!(m("a"), [lp_px(5), lp_px(10), lp_px(10), lp_px(10)]);
    assert_eq!(m("b"), [lp_px(10); 4]);
    assert_eq!(m("c"), [lp_px(10), lp_px(10), lp_px(10), lp_px(3)]);
    assert_eq!(m("d"), [lp_px(10); 4]);
    assert_eq!(
        m("e"),
        [lp_px(10), lp_px(10), lp_px(10), lp_px(3)],
        "important longhand wins"
    );
}

/// CSS Logical Properties 1 §4.1†: a flow-relative property and its physical counterpart
/// "share a computed value": the one declared later in cascade order wins, with specificity
/// deciding first. In `horizontal-tb` and `ltr`, `margin-inline-start` is `margin-left` and
/// `margin-block-end` is `margin-bottom` (Writing Modes 4 §6.4†).
#[test]
fn logical_and_physical_order() {
    let html = "<!DOCTYPE html><style>\
                #a { margin-left: 5px; margin-inline-start: 7px }\
                #b { margin-inline-start: 7px; margin-left: 5px }\
                .c { margin-inline-start: 7px } #c { margin-left: 5px }\
                #d { margin-left: 5px } .d { margin-inline-start: 7px }\
                #e { margin-block-end: 9px; margin-bottom: 4px; margin-inline-end: 2px }\
                </style>\
                <div id=a></div><div id=b></div><div id=c class=c></div><div id=d class=d></div>\
                <div id=e></div>";
    let doc = Doc::new(html);
    let m = |id| doc.style(id).margin;
    assert_eq!(m("a")[3], lp_px(7), "later logical");
    assert_eq!(m("b")[3], lp_px(5), "later physical");
    assert_eq!(
        m("c")[3],
        lp_px(5),
        "the id's physical beats the class's logical"
    );
    assert_eq!(
        m("d")[3],
        lp_px(5),
        "specificity (1,0,0) beats a later (0,1,0)"
    );
    assert_eq!(m("e")[2], lp_px(4), "the later physical margin-bottom");
    assert_eq!(m("e")[1], lp_px(2), "inline end is right");
}

/// Selectors 4 §17: ":is() and :not() ... specificity is that of its most specific
/// argument", and ":where() ... specificity is replaced by zero".
#[test]
fn is_where_not_specificity() {
    // `:is(.x, #a)` counts as (1,0,0) (its most specific argument), even though the element
    // also matches `.x`; it beats `.x.y` (0,2,0) although it comes first.
    let html = "<!DOCTYPE html><style>:is(.x, #a) { color: red } .x.y { color: green }</style>\
                <p id=a class='x y'>1</p>";
    assert_eq!(color_of(html, "a"), RED);
    // `:where(#a)` is (0,0,0): the earlier `p` (0,0,1) beats the later `:where`.
    let html = "<!DOCTYPE html><style>p { color: green } :where(#a) { color: red }</style>\
                <p id=a>1</p>";
    assert_eq!(color_of(html, "a"), GREEN);
    // `p:where(#a)` is (0,0,1), the same as `p`: order decides.
    let html = "<!DOCTYPE html><style>p { color: green } p:where(#a) { color: red }</style>\
                <p id=a>1</p>";
    assert_eq!(color_of(html, "a"), RED);
    // `:not(#zz)` is (1,0,0): it beats `.x.y` (0,2,0), and matches (the id is not zz).
    let html = "<!DOCTYPE html><style>:not(#zz) { color: red } .x.y { color: green }</style>\
                <p id=a class='x y'>1</p>";
    assert_eq!(color_of(html, "a"), RED);
    // `:not(.q, #zz)` takes the more specific argument: (1,0,0) as well.
    let html = "<!DOCTYPE html><style>:not(.q, #zz) { color: red } .x.y { color: green }</style>\
                <p id=a class='x y'>1</p>";
    assert_eq!(color_of(html, "a"), RED);
    // `:is(.x)` is (0,1,0), the same as `.y`: order decides.
    let html = "<!DOCTYPE html><style>:is(.x) { color: red } .y { color: green }</style>\
                <p id=a class='x y'>1</p>";
    assert_eq!(color_of(html, "a"), GREEN);
}

/// HTML §4.6.8.23 and CSSOM §6.2: a `<link rel=stylesheet>` sheet, once loaded, is a style
/// sheet of the document in tree order, so it cascades with the `<style>` elements around it
/// by order of appearance.
#[test]
fn linked_sheet_cascades_in_tree_order() {
    use crate::sources::Response;
    use clazel_encoding::labels::spec::Encoding;
    let html = "<!DOCTYPE html><style>.c { color: red }</style>\
                <link rel=stylesheet href=a.css>\
                <style>.d { color: blue }</style><p id=a class=c>x</p><p id=b class='c d'>y</p>";
    let arena = parse(html);
    let mut sources = collect(&arena);
    assert_eq!(sources.pending_links(), [1]);
    let device = Device::screen(800, 600);
    let a = by_id(&arena, "a").unwrap_or(0);
    let b = by_id(&arena, "b").unwrap_or(0);
    // Before the response, the link contributes nothing.
    let before = cascade(&arena, &sources, device);
    assert_eq!(before.get(a).map(|s| s.color), Some(RED));
    let response = |ok| Response {
        content_type: Some(b"text/css"),
        same_origin: true,
        ok,
        body: b".c { color: green }",
    };
    sources.link_loaded(1, response(true), Encoding::Utf8);
    let after = cascade(&arena, &sources, device);
    // The link follows the first `<style>`: its `.c` wins there; the second `<style>`'s
    // `.d` follows both.
    assert_eq!(after.get(a).map(|s| s.color), Some(GREEN));
    assert_eq!(after.get(b).map(|s| s.color), Some(BLUE));
    // A failed response leaves the first sheet's result.
    let mut failed = collect(&arena);
    failed.link_loaded(1, response(false), Encoding::Utf8);
    let table = cascade(&arena, &failed, device);
    assert_eq!(table.get(a).map(|s| s.color), Some(RED));
}

/// Quirks Mode Standard §3.6, §3.7: the unitless length and hashless colour quirks apply in
/// quirks mode only. A document whose doctype puts it in limited-quirks mode (HTML §13.2.6.4.1:
/// the XHTML 1.0 Transitional public identifier) cascades with the quirk off, as a no-quirks
/// document does, and a document with no doctype (quirks) with it on.
#[test]
fn limited_quirks_mode_is_off() {
    let body = "<style>td { width: 10; color: f00 } #p { margin-left: 5 }</style>\
                <table><tr><td id=d>x</td></tr></table><p id=p>y</p>";
    let limited = "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \
                   \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">";
    let none = "<!DOCTYPE html>";
    for (doctype, mode, quirks) in [
        ("", "quirks", true),
        (limited, "limited-quirks", false),
        (none, "no-quirks", false),
    ] {
        // Under Miri a document takes over a minute: only the mode this test is for.
        if cfg!(miri) && mode != "limited-quirks" {
            continue;
        }
        let html = format!("{doctype}{body}");
        let arena = parse(&html);
        let got = match arena.kind(0) {
            ExecKind::Document {
                mode: DocumentMode::Quirks,
                ..
            } => "quirks",
            ExecKind::Document {
                mode: DocumentMode::LimitedQuirks,
                ..
            } => "limited-quirks",
            ExecKind::Document {
                mode: DocumentMode::NoQuirks,
                ..
            } => "no-quirks",
            _ => "not a document",
        };
        assert_eq!(got, mode, "{doctype:?}");
        assert_eq!(collect(&arena).quirks, quirks, "{mode}");
        let doc = Doc::new(&html);
        let d = doc.style("d");
        if quirks {
            assert_eq!(d.width, lp_px(10), "{mode}: unitless length");
            assert_eq!(d.color, RED, "{mode}: hashless colour");
            assert_eq!(doc.style("p").margin[3], lp_px(5), "{mode}");
        } else {
            assert_eq!(d.width, Size::Auto, "{mode}: the declaration is dropped");
            assert_eq!(d.color, BLACK, "{mode}: the declaration is dropped");
            assert_eq!(doc.style("p").margin[3], lp_px(0), "{mode}");
        }
    }
}

/// CSS Fonts 4 §2.2: `font-weight` is `normal | bold | <number [1,1000]> | bolder | lighter`,
/// so a number outside 1 to 1000 makes the declaration invalid, and it is dropped (CSS Syntax
/// 3 §5.4.4's error handling): the element keeps the inherited weight. This is what makes
/// `font_weight_any`'s assumption (an inherited weight in 1 to 1000) true: no path of the
/// cascade computes a weight outside the range. `bolder` and `lighter` (§2.2.1's table, for
/// an inherited 700: 900 and 400) stay inside it too.
#[test]
fn font_weight_stays_in_one_to_one_thousand() {
    let weight = |decl: &str| {
        let html = format!(
            "<!DOCTYPE html><div style='font-weight: 700'>\
             <p id=p style='font-weight: {decl}'>x</p></div>"
        );
        Doc::new(&html).style("p").font_weight
    };
    let n = |v: i64| Num {
        millionths: v,
        is_integer: v % 1_000_000 == 0,
    };
    // Under Miri a document takes most of a minute: one value of each kind.
    if cfg!(miri) {
        assert_eq!(weight("1000"), n(1_000_000_000));
        assert_eq!(weight("1000.000001"), n(700_000_000));
        return;
    }
    // In range: kept as written.
    assert_eq!(weight("1"), n(1_000_000));
    assert_eq!(weight("1000"), n(1_000_000_000));
    assert_eq!(weight("550.5"), n(550_500_000));
    // Out of range: dropped, so the parent's 700 is inherited.
    for bad in [
        "0",
        "0.999999",
        "-1",
        "1000.000001",
        "1001",
        "99999999",
        "1e4",
        "-0",
    ] {
        assert_eq!(weight(bad), n(700_000_000), "{bad}");
    }
    assert_eq!(weight("bolder"), n(900_000_000));
    assert_eq!(weight("lighter"), n(400_000_000));
}

/// Item 6.11: the `background-*` longhands compute (CSS Backgrounds 3 §2.1, §2.4, §2.6,
/// §2.9).
#[test]
fn background_layers_compute() {
    // A document parse and a cascade: about 0.01 s natively, over the 0.002 s a Miri test may
    // take (CI measured Miri 25,000 to 30,000 times slower); the arithmetic is covered natively.
    if cfg!(miri) {
        return;
    }
    let d = Doc::new(
        "<!DOCTYPE html><div id=a style=\"background-image: url(x.png), url(y.png); \
         background-repeat: no-repeat, repeat-x; background-position: right 10px; \
         background-size: 50% auto\"></div><div id=b></div>\
         <div id=c style=\"background-image: url(p.png), none, linear-gradient(red, blue); \
         background-repeat: space round; background-position: bottom; \
         background-size: cover, contain; background-clip: content-box\"></div>",
    );
    // The initial layer.
    let b = d.style("b").backgrounds;
    assert_eq!(b, Backgrounds::initial());
    assert!(b.is_none());
    let url = |s: &str| BgImage::Url(s.chars().map(u32::from).collect());
    let pct = |n: i64| Lp::Percent(Num::from_int(n));
    // Two layers (the first is closest to the user): `no-repeat` is both axes (§2.4) and
    // `repeat-x` is `repeat no-repeat`; the lists of one value are repeated for the second
    // layer (§2.1); `right 10px` is 100% horizontally and 10px vertically (§2.6).
    let a = d.style("a").backgrounds.layers();
    assert_eq!(
        a.iter().map(|l| l.image.clone()).collect::<Vec<_>>(),
        vec![url("x.png"), url("y.png")]
    );
    assert_eq!(
        a.iter().map(|l| l.repeat).collect::<Vec<_>>(),
        vec![
            [BgRepeat::NoRepeat; 2],
            [BgRepeat::Repeat, BgRepeat::NoRepeat]
        ]
    );
    assert_eq!(
        a.iter().map(|l| l.position).collect::<Vec<_>>(),
        vec![[pct(100), Lp::Px64(10 * 64)]; 2]
    );
    assert_eq!(
        a.iter().map(|l| l.size).collect::<Vec<_>>(),
        vec![BgSize::Explicit([Some(pct(50)), None]); 2]
    );
    // §2.1: three layers (a gradient is a layer that paints nothing); the lists repeat.
    let c = d.style("c").backgrounds.layers();
    assert_eq!(
        c.iter().map(|l| l.image.clone()).collect::<Vec<_>>(),
        vec![url("p.png"), BgImage::None, BgImage::None]
    );
    assert_eq!(
        c.iter().map(|l| l.repeat).collect::<Vec<_>>(),
        vec![[BgRepeat::Space, BgRepeat::Round]; 3]
    );
    // §2.6: a single `bottom` is `50% 100%`.
    assert_eq!(
        c.iter().map(|l| l.position).collect::<Vec<_>>(),
        vec![[pct(50), pct(100)]; 3]
    );
    // §2.9: `cover, contain` repeated for the third layer.
    assert_eq!(
        c.iter().map(|l| l.size).collect::<Vec<_>>(),
        vec![BgSize::Cover, BgSize::Contain, BgSize::Cover]
    );
    assert_eq!(
        c.iter().map(|l| (l.origin, l.clip)).collect::<Vec<_>>(),
        vec![(BgBox::Padding, BgBox::Content); 3]
    );
}

/// Item 6.11: a `url()` in a sheet is relative to the sheet's URL, in a `style` element or
/// attribute to the document's (CSS Values 4 §4.5).
#[test]
fn background_urls_resolve_against_their_sheet() {
    // As above: skipped under Miri; `urls::tests` cover the resolution there.
    if cfg!(miri) {
        return;
    }
    let arena = parse(
        "<!DOCTYPE html><link rel=stylesheet href=s/a.css>\
         <style>#e { background-image: url(i/e.png) }</style>\
         <div id=l></div><div id=e></div><div id=s style=\"background-image: url(s.png)\"></div>",
    );
    let code = |s: &str| s.chars().map(u32::from).collect::<Vec<u32>>();
    let mut sources = collect(&arena);
    sources.document_url = Some(code("http://example.com/dir/page.html"));
    let sheet = crate::sources::StyleSheet::parse(&code("#l { background-image: url(../l.png) }"));
    for s in &mut sources.sheets {
        if matches!(s.owner, crate::sources::Owner::Link(_)) {
            s.sheet = Some(sheet.clone());
            s.url = Some(code("http://cdn.test/css/s/a.css"));
        }
    }
    let device = Device::screen(800, 600);
    let table = if cfg!(miri) {
        cascade_with(&ua::sheets().for_document(&arena), &arena, &sources, device)
    } else {
        cascade(&arena, &sources, device)
    };
    let url_of = |id: &str| -> String {
        let urls = by_id(&arena, id)
            .and_then(|n| table.get(n))
            .map(|s| s.backgrounds.image.clone())
            .unwrap_or_default();
        match urls.as_slice() {
            [BgImage::Url(u)] => u.iter().filter_map(|&c| char::from_u32(c)).collect(),
            _ => String::new(),
        }
    };
    assert_eq!(url_of("l"), "http://cdn.test/css/l.png");
    assert_eq!(url_of("e"), "http://example.com/dir/i/e.png");
    assert_eq!(url_of("s"), "http://example.com/dir/s.png");
}
