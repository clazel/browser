//! Tests of item 6.11: natural sizes from [`Images`], broken images' `alt` text, and
//! background images, through layout and paint.
//!
//! As in `flow/tests.rs`: documents are parsed by the HTML tree builder, cascaded with a
//! small user agent sheet (`display` only) and laid out with [`BoxFont`] (every glyph an em
//! square). The documents use a 10px font, so a character is 10px wide and a line 10px
//! high. Each expectation is worked out by hand in the comment above it.
//!
//! WPT's `css/CSS2/` replaced-element and `css/css-backgrounds/` reftests cannot run here:
//! they need an image decoder (items 6.4 to 6.8) and `browse --headless` (item 5.25 waits
//! for it, `crates/clazel/tests/reftests.rs`), and the classifier counts a test that
//! names `url(` or an `img` as not run. These tests state the same expectations as
//! rectangles and display list items instead.
//!
//! Miri: see [`miri_skip`].

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::hints::attribute;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

use crate::boxes::{BoxTree, Class, build_with_images};
use crate::flow::fragment::Rect;
use crate::flow::{BoxFont, FragmentTree, Viewport, layout_with_images};
use crate::images::{Dims, ImageStatus, Images};
use crate::paint::dump::dump;
use crate::paint::{Resources, paint_with_images};

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

const UA: &str = "html, body, div, p { display: block } head, style, title { display: none }";

/// Under Miri (CI measured it 25,000 to 30,000 times slower than native debug) none of these
/// runs: each is a document parse, a cascade, a layout and a paint, about 0.01 s natively,
/// over the 0.002 s a Miri test may take. The code they reach that is pure arithmetic
/// (sizes, positions and tiles) has Miri tests of its own in `paint/background.rs`, each
/// microseconds natively; the walks run natively in CI.
fn miri_skip(_index: u32) -> bool {
    cfg!(miri)
}

struct Laid {
    arena: Arena,
    tree: BoxTree,
    frags: FragmentTree,
    list: String,
}

const DOC_URL: &str = "http://example.com/dir/page.html";

fn lay(html: &str, images: &Images, scale: u32) -> Laid {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let arena = parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena;
    let mut sources = collect(&arena);
    sources.document_url = Some(DOC_URL.chars().map(u32::from).collect());
    let code: Vec<u32> = UA.chars().map(u32::from).collect();
    let sheets = ua::Sheets {
        ua: StyleSheet::parse(&code),
        ua_quirks: StyleSheet::parse(&[]),
        hints: StyleSheet::parse(&[]),
    };
    let table = cascade_with(&sheets, &arena, &sources, Device::screen(400, 300));
    let tree = build_with_images(&arena, &table, images);
    let frags = layout_with_images(
        &tree,
        &arena,
        images,
        &table,
        &BoxFont,
        Viewport::px(400, 300),
    );
    let url: Vec<u32> = DOC_URL.chars().map(u32::from).collect();
    let base = clazel_url::url::parse::basic_url_parser(&url, None);
    let list = paint_with_images(
        &frags,
        &tree,
        &arena,
        &table,
        &BoxFont,
        Resources {
            base: base.as_ref(),
            images,
            controls: &[],
        },
        scale,
    );
    Laid {
        arena,
        tree,
        frags,
        list: dump(&list),
    }
}

const STD: &str = "<!DOCTYPE html><style>html { font-size: 10px } body { margin: 0 }</style>";

fn std(body: &str, images: &Images) -> Laid {
    lay(&format!("{STD}{body}"), images, 1)
}

fn px(n: i32) -> i32 {
    n.saturating_mul(64)
}

fn node_by_id(arena: &Arena, id: &str) -> usize {
    (0..arena.len())
        .find(|&n| match arena.kind(n) {
            ExecKind::Element { attributes, .. } => attribute(attributes, "id")
                .is_some_and(|v| v.iter().copied().eq(id.chars().map(u32::from))),
            _ => false,
        })
        .unwrap_or(usize::MAX)
}

/// The box element `id` generates.
fn box_of(l: &Laid, id: &str) -> Option<usize> {
    let node = node_by_id(&l.arena, id);
    (0..l.tree.boxes.len()).find(|&b| l.tree.get(b).and_then(|x| x.node) == Some(node))
}

/// The border box of the box element `id` generates (empty if there is none).
fn border_box(l: &Laid, id: &str) -> Rect {
    box_of(l, id)
        .and_then(|b| l.frags.fragment(b))
        .map(|f| f.border_box)
        .unwrap_or_default()
}

fn sized(w: u32, h: u32) -> ImageStatus {
    ImageStatus::Sized {
        natural: Dims {
            width: w,
            height: h,
        },
    }
}

fn ready(id: u32, w: u32, h: u32) -> ImageStatus {
    ImageStatus::Ready {
        id,
        natural: Dims {
            width: w,
            height: h,
        },
        pixels: Dims {
            width: w,
            height: h,
        },
    }
}

/// An `img` with no attributes is 0 by 0 until its config arrives (HTML §15.4.2: "a replaced
/// element whose natural dimensions are 0"), then its natural size (CSS 2.1 §10.3.2 rule 1,
/// §10.6.2 rule 1); the same document laid out again with the map updated.
#[test]
fn natural_size_once_the_config_arrives() {
    if miri_skip(0) {
        return;
    }
    let doc = "<div><img id=i></div>";
    let node = node_by_id(&std(doc, &Images::new()).arena, "i");
    let before = std(doc, &Images::new());
    assert_eq!(border_box(&before, "i").width, 0);
    assert_eq!(border_box(&before, "i").height, 0);
    let mut images = Images::new();
    images.set_element(node, sized(40, 20));
    let after = std(doc, &images);
    // 40 by 20 px, at the left of the first line.
    let b = border_box(&after, "i");
    assert_eq!((b.x, b.width, b.height), (0, px(40), px(20)));
    // Ready (pixels uploaded) is sized the same way.
    images.set_element(node, ready(3, 40, 20));
    assert_eq!(border_box(&std(doc, &images), "i").width, px(40));
}

/// §10.3.2 rule 2 and §10.6.2 rule 2: "(used height) * (intrinsic ratio)" and "(used width)
/// / (intrinsic ratio)" when one side is given; a given width and height are used as they
/// are; `max-width` clamps the width and the height follows.
#[test]
fn the_natural_ratio_fills_in_the_other_side() {
    if miri_skip(3) {
        return;
    }
    let doc = "<div><img id=w width=20><img id=h height=10><img id=b width=7 height=9>\
               <img id=m style='max-width: 30px'><img id=n style='min-height: 40px'></div>";
    let node = node_by_id(&std(doc, &Images::new()).arena, "w");
    let mut images = Images::new();
    for id in ["w", "h", "b", "m", "n"] {
        let n = node_by_id(&std(doc, &Images::new()).arena, id);
        images.set_element(n, sized(40, 20));
    }
    let _ = node;
    let l = std(doc, &images);
    // 40:20 is 2:1: width 20 gives height 10.
    assert_eq!(
        (border_box(&l, "w").width, border_box(&l, "w").height),
        (px(20), px(10))
    );
    // Height 10 gives width 20.
    assert_eq!(
        (border_box(&l, "h").width, border_box(&l, "h").height),
        (px(20), px(10))
    );
    // Both given: as given.
    assert_eq!(
        (border_box(&l, "b").width, border_box(&l, "b").height),
        (px(7), px(9))
    );
    // max-width: 30px on 40 by 20: width 30, height 15.
    assert_eq!(
        (border_box(&l, "m").width, border_box(&l, "m").height),
        (px(30), px(15))
    );
    // min-height: 40px on 40 by 20: height 40; the width stays the natural 40 (the table of
    // CSS 2.1 §10.4 would keep the ratio, listed in `flow/replaced.rs`).
    assert_eq!(
        (border_box(&l, "n").width, border_box(&l, "n").height),
        (px(40), px(40))
    );
}

/// A block-level image (`display: block`) is sized as an inline one (§10.3.4: "The used
/// value of 'width' is determined as for inline replaced elements"), and `width: 100%` with
/// a ratio takes its height from the width.
#[test]
fn block_level_images() {
    if miri_skip(6) {
        return;
    }
    let doc = "<div style='width: 200px'><img id=i style='display: block; width: 100%'></div>";
    let node = node_by_id(&std(doc, &Images::new()).arena, "i");
    let mut images = Images::new();
    images.set_element(node, sized(40, 20));
    let l = std(doc, &images);
    assert_eq!(
        (border_box(&l, "i").width, border_box(&l, "i").height),
        (px(200), px(100))
    );
}

/// HTML §15.4.2: a broken image with `alt` text is a non-replaced inline box with the text
/// ("abc" is 3 characters of 10px, on a 10px line); an empty `alt` is an empty inline
/// element; no `alt` is the replaced element of size 0 by 0; a pending image keeps its
/// replaced box (the user agent "has reason to believe that the image will become
/// available").
#[test]
fn broken_images_show_their_alt() {
    if miri_skip(9) {
        return;
    }
    let doc = "<div><img id=a alt=abc><img id=e alt=''><img id=n><img id=p alt=pending></div>";
    let probe = std(doc, &Images::new());
    let mut images = Images::new();
    for id in ["a", "e", "n"] {
        images.set_element(node_by_id(&probe.arena, id), ImageStatus::Broken);
    }
    let l = std(doc, &images);
    let class = |id: &str| box_of(&l, id).map(|b| l.tree.class(b));
    assert_eq!(class("a"), Some(Class::Inline));
    assert_eq!(class("e"), Some(Class::Inline));
    assert_eq!(class("n"), Some(Class::Replaced { inline: true }));
    assert_eq!(class("p"), Some(Class::Replaced { inline: true }));
    // The text: 3 characters at 10px, in the first line box.
    assert!(
        l.list.contains("glyphs=3"),
        "the alt text is painted: {}",
        l.list
    );
    assert_eq!(border_box(&l, "n").width, 0);
    // `a` starts the line; `e`, `n` and `p` follow it, so `n` starts at 30px (`e` is empty).
    assert_eq!(border_box(&l, "n").x, px(30));
}

/// A broken image whose size the page gives, in quirks mode, stays a replaced element
/// (HTML §15.4.2: "the element already has intrinsic dimensions ... and either ... the
/// Document is in quirks mode"), sized as given; in no-quirks mode it shows its text.
#[test]
fn broken_images_with_dimensions_in_quirks_mode() {
    if miri_skip(12) {
        return;
    }
    let body = "<img id=i alt=abc width=50 height=30>";
    let sheet = "<style>html { font-size: 10px } body { margin: 0 }</style>";
    let probe = lay(&format!("{sheet}{body}"), &Images::new(), 1);
    let mut images = Images::new();
    images.set_element(node_by_id(&probe.arena, "i"), ImageStatus::Broken);
    let quirks = lay(&format!("{sheet}{body}"), &images, 1);
    assert_eq!(
        (
            border_box(&quirks, "i").width,
            border_box(&quirks, "i").height
        ),
        (px(50), px(30))
    );
    let probe = std(body, &Images::new());
    let mut images = Images::new();
    images.set_element(node_by_id(&probe.arena, "i"), ImageStatus::Broken);
    let standard = std(body, &images);
    assert_eq!(
        box_of(&standard, "i").map(|b| standard.tree.class(b)),
        Some(Class::Inline)
    );
}

/// An `img` whose pixels are uploaded paints one image item over its content box; before
/// that, nothing. At scale 2 the destination doubles, and the draw is linear (it is not the
/// image's own size); at scale 1 it is the image's size, so nearest.
#[test]
fn an_img_paints_an_image_item() {
    if miri_skip(15) {
        return;
    }
    let doc = "<div style='padding: 5px'><img id=i style='border: 2px solid; padding: 1px'></div>";
    let probe = std(doc, &Images::new());
    let node = node_by_id(&probe.arena, "i");
    let mut images = Images::new();
    images.set_element(node, sized(40, 20));
    assert!(!std(doc, &images).list.contains("image "));
    images.set_element(node, ready(3, 40, 20));
    // The div's padding 5, the image's border 2 and padding 1: its content box is at (8, 8),
    // 40 by 20.
    let l = std(doc, &images);
    assert!(
        l.list
            .contains("image 8,8 40x20 id=3 src=0,0 40x20 nearest"),
        "{}",
        l.list
    );
    let l2 = lay(&format!("{STD}{doc}"), &images, 2);
    assert!(
        l2.list
            .contains("image 16,16 80x40 id=3 src=0,0 40x20 linear"),
        "{}",
        l2.list
    );
}

fn url_images(urls: &[(&str, ImageStatus)]) -> Images {
    let mut images = Images::new();
    for (u, s) in urls {
        images.set_url(u, *s);
    }
    images
}

const A: &str = "http://example.com/dir/a.png";

/// `background-image: url()`, resolved against the document (the sheet's URL is the
/// document's for a `style` attribute), `no-repeat`, `50% 50%`: one tile at
/// ((100 - 20) / 2, (50 - 10) / 2) in a 100 by 50 box; no clip, since it is inside.
#[test]
fn a_centred_background_image() {
    if miri_skip(18) {
        return;
    }
    let doc = "<div style=\"width: 100px; height: 50px; \
               background: url(a.png) no-repeat 50% 50%\"></div>";
    let l = std(doc, &url_images(&[(A, ready(7, 20, 10))]));
    assert!(
        l.list
            .contains("image 40,20 20x10 id=7 src=0,0 20x10 nearest"),
        "{}",
        l.list
    );
    assert!(!l.list.contains("push-clip"), "{}", l.list);
    // Not yet decoded: nothing (CSS Backgrounds 3 §2.3).
    let l = std(doc, &url_images(&[(A, sized(20, 10))]));
    assert!(!l.list.contains("image "), "{}", l.list);
    // Broken: nothing.
    let l = std(doc, &url_images(&[(A, ImageStatus::Broken)]));
    assert!(!l.list.contains("image "), "{}", l.list);
}

/// `repeat` over a 100 by 50 box: 30 by 20 tiles, 4 columns by 3 rows, the last column and
/// the last row overflowing, so the tiles are clipped to the painting area (the border box
/// by default, §2.7) and the clip ends after them. 12 image items.
#[test]
fn a_repeated_background_is_clipped_to_the_painting_area() {
    if miri_skip(21) {
        return;
    }
    let doc = "<div style=\"width: 100px; height: 50px; background-image: url(a.png)\"></div>";
    let l = std(doc, &url_images(&[(A, ready(7, 30, 20))]));
    assert_eq!(l.list.matches("image ").count(), 12, "{}", l.list);
    assert!(l.list.contains("push-clip 0,0 100x50"), "{}", l.list);
    assert!(l.list.contains("image 90,40 30x20"), "{}", l.list);
    let push = l.list.find("push-clip").unwrap_or(usize::MAX);
    let first = l.list.find("image ").unwrap_or(0);
    let pop = l.list.find("pop-clip").unwrap_or(0);
    let last = l.list.rfind("image ").unwrap_or(usize::MAX);
    assert!(push < first && last < pop, "{}", l.list);
}

/// §2.1: layers are painted last to first (the first is on top); the colour is below all of
/// them; `background-origin: content-box` positions in the content box (padding 10 puts it
/// at (10, 10)), `background-clip: content-box` paints only there (a clip of 10,10 80x30
/// for a 100 by 50 box with 10px padding all round... here 80 by 30 content).
#[test]
fn layers_origin_and_clip() {
    if miri_skip(24) {
        return;
    }
    let b = "http://example.com/dir/b.png";
    let doc = "<div style=\"width: 80px; height: 30px; padding: 10px; background-color: red; \
               background-image: url(a.png), url(b.png); background-repeat: no-repeat; \
               background-origin: content-box; background-clip: content-box, border-box\"></div>";
    let l = std(
        doc,
        &url_images(&[(A, ready(1, 100, 10)), (b, ready(2, 10, 10))]),
    );
    // The colour is clipped by the bottom-most layer's clip: the border box (100 by 50).
    let fill = l.list.find("fill 0,0 100x50").unwrap_or(usize::MAX);
    // The bottom layer (b.png, border-box clip, positioned in the content box: (10, 10)).
    let second = l.list.find("id=2").unwrap_or(usize::MAX);
    // The top layer (a.png) is 100 wide: wider than the 80 content box, so it is clipped
    // to the content box (10,10 80x30).
    let first = l.list.find("id=1").unwrap_or(0);
    assert!(fill < second && second < first, "{}", l.list);
    assert!(l.list.contains("image 10,10 10x10 id=2"), "{}", l.list);
    assert!(l.list.contains("image 10,10 100x10 id=1"), "{}", l.list);
    assert!(l.list.contains("push-clip 10,10 80x30"), "{}", l.list);
}

/// §2.11.2: the `body`'s background propagates to the canvas when the `html` element's is
/// `none` and transparent; §2.11.1: its images are positioned in the root element's box and
/// painted over the whole canvas. With `repeat-y` and an 8 px wide image at `100% 0`, the
/// column of tiles sits at the right edge of the root element's box (400 wide: x = 392).
#[test]
fn the_body_background_goes_to_the_canvas() {
    if miri_skip(27) {
        return;
    }
    let doc = "<body style=\"margin: 0; height: 20px; background: url(a.png) repeat-y 100% 0\">";
    let l = lay(
        &format!("<!DOCTYPE html><style>html {{ font-size: 10px }}</style>{doc}"),
        &url_images(&[(A, ready(5, 8, 10))]),
        1,
    );
    // The canvas covers the viewport (400 by 300): 30 tiles of 10px in the column, the root
    // element's box being only as high as its content (20px), so tiles continue past it.
    assert!(l.list.contains("image 392,0 8x10 id=5"), "{}", l.list);
    assert!(l.list.contains("image 392,290 8x10 id=5"), "{}", l.list);
    assert_eq!(l.list.matches("image ").count(), 30, "{}", l.list);
}
