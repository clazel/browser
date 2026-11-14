//! The cascade end to end: documents parsed by `clazel-treebuilder`, their sources collected
//! by `sources::collect`, cascaded.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use super::computed::*;
use super::*;
use crate::sources::collect;
use crate::values::number::Num;

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
