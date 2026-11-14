//! Tests of the graphical pipeline: documents through [`crate::run_graphics`]
//! to encoded display lists that `clazel-displaylist`'s validator accepts,
//! drawn to pixels by `clazel-gpu`'s software backend.

use std::io::Cursor;

use clazel_displaylist::exec::{ExecItem, Validator, decode};
use clazel_gpu::soft::SoftBackend;
use clazel_gpu::start::Launch;
use clazel_gpu::{Gpu, Viewport};
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};

use super::fonts::Fonts;
use super::state::SheetWait;
use crate::{RunError, run_graphics};

const DEJAVU: &[u8] =
    include_bytes!("../../../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf");

fn fonts() -> Fonts {
    // The embedded bytes, not a leaked copy: Miri reports each leak.
    Fonts::from_static(vec![DEJAVU])
}

fn frames(msgs: &[Msg]) -> Vec<u8> {
    msgs.iter()
        .flat_map(|m| encode_framed(m).unwrap_or_default())
        .collect()
}

/// The frames that commit `body` as `content_type`.
fn commit(body: &str, content_type: &str) -> Vec<Msg> {
    vec![
        Msg::Commit {
            url: b"http://a.example/dir/page".to_vec(),
            content_type: content_type.as_bytes().to_vec(),
            kind: 0,
        },
        Msg::Body {
            bytes: body.as_bytes().to_vec(),
        },
        Msg::BodyEnd,
    ]
}

fn viewport(width: u64, height: u64) -> Msg {
    Msg::Viewport {
        width,
        height,
        scale: 1,
    }
}

/// What the renderer sent: the kernel's messages, and the lists.
struct Sent {
    kernel: Vec<Msg>,
    lists: Vec<Vec<ExecItem>>,
    raw: Vec<Vec<u8>>,
}

/// The frames of `bytes`: each a 4-byte big-endian length and that many
/// bytes.
fn split_frames(bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut rest = bytes;
    while let Some((head, tail)) = rest.split_first_chunk::<4>() {
        let len = usize::try_from(u32::from_be_bytes(*head)).unwrap_or(usize::MAX);
        let Some(body) = tail.get(..len) else { break };
        out.push(body.to_vec());
        rest = tail.get(len..).unwrap_or_default();
    }
    out
}

/// Run `input` through the graphical renderer with the vendored DejaVu
/// Serif.
fn run(input: &[Msg]) -> Result<Sent, RunError> {
    let mut w = Vec::new();
    let mut list = Vec::new();
    run_graphics(&mut Cursor::new(frames(input)), &mut w, &mut list, &fonts())?;
    // The kernel's frames keep their length prefix for `decode_framed`.
    let kernel = split_frames(&w)
        .into_iter()
        .filter_map(|body| {
            let mut frame = u32::try_from(body.len())
                .unwrap_or(0)
                .to_be_bytes()
                .to_vec();
            frame.extend_from_slice(&body);
            decode_framed(&frame)
        })
        .collect();
    // The lists as the GPU process reads them (`clazel_gpu::channel`).
    let mut raw = Vec::new();
    let mut rest = &list[..];
    while let Ok(Some(l)) = clazel_gpu::channel::read_list(&mut rest) {
        raw.push(l);
    }
    assert!(rest.is_empty(), "bytes left after the last list");
    let lists = raw.iter().map(|b| decode(b).unwrap_or_default()).collect();
    Ok(Sent { kernel, lists, raw })
}

/// Every list the renderer sent passes the validator, in order, with the
/// masks of earlier lists live, as in the GPU process.
fn all_valid(s: &Sent) -> bool {
    let mut v = Validator::empty();
    s.lists.iter().all(|l| v.validate(l))
}

/// The RGBA pixels of the lists drawn in order by the software backend,
/// the last frame's.
fn draw(s: &Sent, width: u32, height: u32) -> Vec<u8> {
    let Ok((mut gpu, _)) = Gpu::start_with(SoftBackend::new(), Launch::SOFTWARE, b"") else {
        return Vec::new();
    };
    let Some(vp) = Viewport::new(width, height) else {
        return Vec::new();
    };
    for bytes in &s.raw {
        if gpu.draw(bytes, vp).is_err() {
            return Vec::new();
        }
    }
    let mut out = Vec::new();
    let _ = clazel_gpu::Backend::read_pixels(gpu.backend(), &mut out);
    out
}

fn pixel(px: &[u8], width: u32, x: u32, y: u32) -> [u8; 4] {
    let at = y
        .checked_mul(width)
        .and_then(|v| v.checked_add(x))
        .and_then(|v| v.checked_mul(4))
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or(usize::MAX);
    px.get(at..at.saturating_add(4))
        .and_then(|p| <[u8; 4]>::try_from(p).ok())
        .unwrap_or([0, 0, 0, 0])
}

fn count(l: &[ExecItem], f: fn(&ExecItem) -> bool) -> usize {
    l.iter().filter(|i| f(i)).count()
}

const STYLED: &str = "<!DOCTYPE html><title>  A \n page </title>\
<style>body { margin: 0; background: #ff0000 } p { margin: 0; color: #000000 }</style>\
<div style='background: #0000ff; width: 10px; height: 10px'></div><p>Hello</p>";

/// The renderer's list socket and the GPU process agree: the bytes the renderer
/// writes go through the GPU process's own loop (`clazel_gpu::process::Server`:
/// its reader's framing, 5.17a's decoder and validator, the batching) and draw
/// the same pixels the test's own draw gives.
#[test]
fn the_gpu_process_reads_what_the_renderer_writes() -> Result<(), RunError> {
    let mut input = commit(STYLED, "text/html");
    input.push(viewport(100, 40));
    let mut w = Vec::new();
    let mut list = Vec::new();
    run_graphics(
        &mut Cursor::new(frames(&input)),
        &mut w,
        &mut list,
        &fonts(),
    )?;
    let started = Gpu::start(SoftBackend::new(), Launch::SOFTWARE).ok();
    assert!(started.is_some());
    let Some((gpu, _)) = started else {
        return Ok(());
    };
    let mut server = clazel_gpu::process::Server::new(gpu);
    let size = encode_framed(&Msg::GpuViewport {
        width: 100,
        height: 40,
        scale: 1,
    })
    .unwrap_or_default();
    assert_eq!(server.kernel(&size), Ok(Vec::new()));
    let mut rest = &list[..];
    let mut frames_drawn = Vec::new();
    while let Ok(Some(l)) = clazel_gpu::channel::read_list(&mut rest) {
        let frame = server.list(&l);
        assert!(matches!(frame, Ok(Some(_))), "{frame:?}");
        frames_drawn.extend(frame.ok().flatten());
    }
    assert!(rest.is_empty());
    assert_eq!(frames_drawn.len(), 1);
    let first = frames_drawn.first().map(|f| f.pixels.clone());
    assert_eq!(first, Some(draw(&run(&input)?, 100, 40)));
    Ok(())
}

/// A document with a `style` element and a `style` attribute, down to a list
/// the validator accepts, drawn: the body's red covers the canvas, the
/// div's blue its 10px square, and "Hello" draws dark pixels below it; the
/// title, stripped and collapsed, goes to the kernel.
#[test]
fn inline_styles_to_pixels() -> Result<(), RunError> {
    let mut input = commit(STYLED, "text/html");
    input.push(viewport(100, 40));
    let s = run(&input)?;
    assert_eq!(
        s.kernel,
        vec![Msg::Title {
            title: b"A page".to_vec()
        }]
    );
    assert_eq!(s.lists.len(), 1);
    assert!(all_valid(&s));
    let l = s.lists.first().cloned().unwrap_or_default();
    assert!(count(&l, |i| matches!(i, ExecItem::UploadMask { .. })) > 0);
    assert!(count(&l, |i| matches!(i, ExecItem::DrawMask { .. })) >= 5);
    let px = draw(&s, 100, 40);
    assert_eq!(pixel(&px, 100, 5, 5), [0, 0, 255, 255]);
    assert_eq!(pixel(&px, 100, 50, 5), [255, 0, 0, 255]);
    // Some pixel of the text row (10 to 30 px down) is darker than red.
    let dark = (10..30).any(|y| (0..60).any(|x| pixel(&px, 100, x, y)[0] < 128));
    assert!(dark);
    Ok(())
}

/// A viewport before the commit paints the commit at once; a new viewport
/// lays the page out again (a narrower one wraps "aaa bbb" to two lines, so
/// its lowest glyph is a line further down); a 0 by 0 one paints
/// nothing.
#[test]
fn viewports_lay_out_again() -> Result<(), RunError> {
    let mut input = vec![viewport(200, 50)];
    input.extend(commit(
        "<!DOCTYPE html><body style='margin:0'>aaa bbb",
        "text/html",
    ));
    input.push(viewport(25, 50));
    input.push(viewport(0, 0));
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 2);
    assert!(all_valid(&s));
    // The lowest glyph: the wrapped second line is a line further down.
    let lowest = |l: &Vec<ExecItem>| {
        l.iter()
            .filter_map(|i| match i {
                ExecItem::DrawMask { y, .. } => Some(*y),
                _ => None,
            })
            .max()
            .unwrap_or(0)
    };
    let (first, second) = (s.lists.first().map(lowest), s.lists.get(1).map(lowest));
    assert!(
        first.zip(second).is_some_and(|(a, b)| b >= a + 10),
        "{first:?} {second:?}"
    );
    // The GPU process keeps the first list's masks: the second uploads only
    // glyphs at new quarter-pixel offsets, fewer than the first.
    let uploads = |l: &Vec<ExecItem>| count(l, |i| matches!(i, ExecItem::UploadMask { .. }));
    let (a, b) = (s.lists.first().map(uploads), s.lists.get(1).map(uploads));
    assert!(a.zip(b).is_some_and(|(a, b)| b < a), "{a:?} {b:?}");
    Ok(())
}

/// A scroll moves the viewport within the page, clamped: a 500px block in
/// a 50px viewport scrolls to 450 at most, and back to 0 at least; a scroll
/// that changes nothing sends no list.
#[test]
fn scrolling_is_clamped() -> Result<(), RunError> {
    let mut input = commit(
        "<!DOCTYPE html><body style='margin:0'><div style='height:500px;background:#00ff00'></div>",
        "text/html",
    );
    input.push(viewport(10, 50));
    let scroll = |negative: bool, delta: u64| Msg::Input {
        kind: 1,
        x: 0,
        y: 0,
        negative,
        delta,
        key: 0,
    };
    input.push(scroll(false, 10_000));
    input.push(scroll(false, 10));
    input.push(scroll(true, 10_000));
    let s = run(&input)?;
    // The first paint, the scroll to 450, the scroll back to 0.
    assert_eq!(s.lists.len(), 3);
    assert!(all_valid(&s));
    // At 450 the green block (0 to 500) covers the viewport from its top.
    let fills: Vec<(i32, u32)> = s.lists.get(1).map_or(Vec::new(), |l| {
        l.iter()
            .filter_map(|i| match i {
                ExecItem::FillRect {
                    y, height, colour, ..
                } if *colour == 0xff00_ff00 => Some((*y, *height)),
                _ => None,
            })
            .collect()
    });
    assert_eq!(fills, vec![(0, 50)]);
    Ok(())
}

/// A click on a link sends `Navigate` with its URL resolved against the
/// document's base URL; a click elsewhere sends nothing.
#[test]
fn clicks_follow_links() -> Result<(), RunError> {
    let mut input = commit(
        "<!DOCTYPE html><body style='margin:0'><a href='next?x=1' style='display:block;height:20px'>go</a>",
        "text/html",
    );
    input.push(viewport(100, 50));
    let click = |y: u64| Msg::Input {
        kind: 0,
        x: 5,
        y,
        negative: false,
        delta: 0,
        key: 0,
    };
    input.push(click(5));
    input.push(click(40));
    let s = run(&input)?;
    let navigations: Vec<&Msg> = s
        .kernel
        .iter()
        .filter(|m| matches!(m, Msg::Navigate { .. }))
        .collect();
    assert_eq!(
        navigations,
        vec![&Msg::Navigate {
            url: b"http://a.example/dir/next?x=1".to_vec()
        }]
    );
    Ok(())
}

/// `text/plain` is one `pre` block of glyphs; another type is a drawn
/// notice; neither has a title.
#[test]
fn plain_text_and_notices_are_drawn() -> Result<(), RunError> {
    for (body, ty) in [
        ("line one\nline two", "text/plain"),
        ("\u{89}PNG", "image/png"),
    ] {
        let mut input = commit(body, ty);
        input.push(viewport(300, 60));
        let s = run(&input)?;
        assert!(all_valid(&s));
        assert_eq!(s.kernel, vec![Msg::Title { title: Vec::new() }]);
        let glyphs = s
            .lists
            .first()
            .map_or(0, |l| count(l, |i| matches!(i, ExecItem::DrawMask { .. })));
        assert!(glyphs > 5, "{ty}");
    }
    Ok(())
}

/// The title is sent when it changes, not again for the same title.
#[test]
fn titles_are_sent_when_they_change() -> Result<(), RunError> {
    let mut input = commit("<title>T</title>x", "text/html");
    input.extend(commit("<title>T</title>y", "text/html"));
    input.extend(commit("<title>U</title>z", "text/html"));
    let s = run(&input)?;
    assert_eq!(
        s.kernel,
        vec![
            Msg::Title {
                title: b"T".to_vec()
            },
            Msg::Title {
                title: b"U".to_vec()
            }
        ]
    );
    // No viewport yet: nothing painted.
    assert!(s.lists.is_empty());
    Ok(())
}

/// The seam for linked sheets (`sheets.rs`): with no fetch, a pending link
/// fails at once and the wait is ready; with fetches, a link whose `media`
/// matches waits until it is answered.
#[test]
fn the_sheet_wait() {
    use clazel_encoding::labels::spec::Encoding;
    use clazel_style::sources::{Device, collect};
    let input: Vec<u32> =
        "<link rel=stylesheet href=a.css><link rel=stylesheet href=b.css media=print>"
            .chars()
            .map(u32::from)
            .collect();
    let arena = clazel_treebuilder::exec::driver::parse_real(
        &crate::pipeline::Encodings,
        &input,
        Vec::new(),
        false,
        false,
    )
    .0
    .arena;
    let device = Device::screen(800, 600);
    let none = SheetWait::start(collect(&arena), device, false, Encoding::Utf8);
    assert!(none.ready() && none.invariant());
    assert!(none.sources.pending_links().is_empty());
    let mut fetch = SheetWait::start(collect(&arena), device, true, Encoding::Utf8);
    // Only the screen link blocks; the print one is not fetched.
    assert_eq!(fetch.pending, vec![0]);
    assert!(!fetch.ready() && fetch.invariant());
    fetch.answer(1, None, Encoding::Utf8);
    assert!(!fetch.ready());
    fetch.answer(0, None, Encoding::Utf8);
    assert!(fetch.ready() && fetch.invariant());
}

/// The HN-shaped fixture (`crates/clazel/tests/fixtures/hn/`) through the
/// pipeline's layout at 800 by 600 to client rectangles (item 5.25's
/// geometry dump): its outer table is 85% of the body's content width or
/// its min-content width, whichever is larger; the dump reads back from its JSON, and compared with
/// itself every rectangle is within the tolerance. Its linked sheet is
/// requested and answered with the fixture's `site.css`.
#[test]
fn the_fixture_to_client_rects() {
    use clazel_layout::rects::{Meta, RectKind, compare, from_json, to_json};
    let html = include_str!("../../../clazel/tests/fixtures/hn/index.html");
    let css = include_str!("../../../clazel/tests/fixtures/hn/site.css");
    let mut page = super::Page::load(b"http://fixture.test/", b"text/html", html.as_bytes(), None);
    // Its one linked sheet is requested, and answered here.
    assert_eq!(page.requests(), vec![(0, b"site.css?v=7".to_vec())]);
    assert!(!page.ready());
    assert!(page.answer(0, Some((b"text/css", css.as_bytes()))));
    let Some(view) = super::View::new(800, 600, 1) else {
        return;
    };
    let rects = page.client_rects(view, &fonts());
    assert!(rects.len() > 100, "{}", rects.len());
    let frame = rects
        .iter()
        .find(|r| r.kind == RectKind::Element && r.name == "table");
    // §3.9.1: the largest of 85% of the body's 784px (666.40625px), the
    // sheet's `#frame { min-width: 796px }` and the table's min-content
    // width (with no spacing, padding or border, the 80-column textarea's).
    let textarea = rects
        .iter()
        .find(|r| r.kind == RectKind::Element && r.name == "textarea")
        .map_or(0, |r| r.rect.width);
    assert_eq!(
        frame.map(|r| r.rect.width),
        Some(textarea.max(42_650).max(796 * 64)),
        "textarea {textarea}"
    );
    let texts = rects.iter().filter(|r| r.kind == RectKind::Text).count();
    assert!(texts > 50, "{texts}");
    let meta = Meta {
        name: "clazel".to_owned(),
        version: "0.0.0".to_owned(),
        date: "2026-11-13".to_owned(),
        viewport: (800, 600, 1),
    };
    let json = to_json(&rects, &meta);
    let read = from_json(&json);
    assert!(read.is_some(), "the dump does not read back");
    let Some((_, back)) = read else { return };
    assert_eq!(back, rects);
    let report = compare(&rects, &back);
    assert_eq!(
        (
            report.compared,
            report.outside,
            report.missing,
            report.extra
        ),
        (rects.len(), 0, 0, 0)
    );
}

/// A linked sheet is render-blocking: `FetchStyle` with the `href` as
/// written, no list until it is answered, then the page with its rules (the
/// sheet's green body); a failed sheet renders the page without it (white).
#[test]
fn linked_sheets_block_rendering_until_answered() -> Result<(), RunError> {
    let page = "<!DOCTYPE html><link rel=stylesheet href='s.css?x'><body style='margin:0'>";
    let canvas = |s: &Sent| {
        s.lists.last().and_then(|l| {
            l.iter().find_map(|i| match i {
                ExecItem::FillRect { colour, .. } => Some(*colour),
                _ => None,
            })
        })
    };
    // Answered: the response, the body in two parts, the end.
    let mut input = vec![viewport(40, 20)];
    input.extend(commit(page, "text/html"));
    input.push(Msg::StyleResponse {
        request: 0,
        content_type: b"text/css; charset=utf-8".to_vec(),
    });
    input.push(Msg::StyleBody {
        request: 0,
        bytes: b"body { backgr".to_vec(),
    });
    input.push(Msg::StyleBody {
        request: 0,
        bytes: b"ound: #00ff00 }".to_vec(),
    });
    input.push(Msg::StyleEnd { request: 0 });
    let s = run(&input)?;
    assert!(s.kernel.contains(&Msg::FetchStyle {
        request: 0,
        url: b"s.css?x".to_vec()
    }));
    // One list: the one painted when the sheet ended.
    assert_eq!(s.lists.len(), 1);
    assert!(all_valid(&s));
    assert_eq!(canvas(&s), Some(0xff00_ff00));
    // Failed: painted without it.
    let mut input = vec![viewport(40, 20)];
    input.extend(commit(page, "text/html"));
    input.push(Msg::StyleFailed { request: 0 });
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 1);
    assert_eq!(canvas(&s), Some(0xffff_ffff));
    // Unanswered: nothing painted, even for a new viewport.
    let mut input = commit(page, "text/html");
    input.push(viewport(40, 20));
    let s = run(&input)?;
    assert!(s.lists.is_empty());
    Ok(())
}

/// A sheet served as another type is not applied in no-quirks mode, and is
/// in quirks mode when same-origin (HTML §4.6.8.23's quirk); a
/// cross-origin one never is.
#[test]
fn the_stylesheet_content_type_quirk() -> Result<(), RunError> {
    let green = |doctype: &str, href: &str| -> Result<bool, RunError> {
        let page = format!("{doctype}<link rel=stylesheet href='{href}'><body style='margin:0'>");
        let mut input = vec![viewport(40, 20)];
        input.extend(commit(&page, "text/html"));
        input.push(Msg::StyleResponse {
            request: 0,
            content_type: b"text/plain".to_vec(),
        });
        input.push(Msg::StyleBody {
            request: 0,
            bytes: b"body { background: #00ff00 }".to_vec(),
        });
        input.push(Msg::StyleEnd { request: 0 });
        let s = run(&input)?;
        Ok(s.lists.last().is_some_and(|l| {
            l.iter().any(|i| {
                matches!(
                    i,
                    ExecItem::FillRect {
                        colour: 0xff00_ff00,
                        ..
                    }
                )
            })
        }))
    };
    assert!(!green("<!DOCTYPE html>", "s.css")?);
    assert!(green("", "s.css")?);
    assert!(!green("", "http://other.example/s.css")?);
    Ok(())
}
