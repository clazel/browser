//! Tests of the graphical pipeline: documents through [`crate::run_graphics`]
//! to encoded display lists that `clazel-displaylist`'s validator accepts,
//! drawn to pixels by `clazel-gpu`'s software backend.

use std::io::{Cursor, Write};
use std::sync::{Arc, Mutex};

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

/// A writer the test can read after the renderer owns it.
#[derive(Clone, Default)]
struct Shared(Arc<Mutex<Vec<u8>>>);

impl Write for Shared {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        if let Ok(mut v) = self.0.lock() {
            v.extend_from_slice(buf);
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl Shared {
    fn bytes(&self) -> Vec<u8> {
        self.0.lock().map(|v| v.clone()).unwrap_or_default()
    }
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
    let w = Shared::default();
    let mut list = Vec::new();
    run_graphics(Cursor::new(frames(input)), w.clone(), &mut list, &fonts())?;
    // The kernel's frames keep their length prefix for `decode_framed`.
    let kernel = split_frames(&w.bytes())
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
    while let Ok(Some((_, l))) = clazel_gpu::channel::read_list(&mut rest) {
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
    let w = Shared::default();
    let mut list = Vec::new();
    run_graphics(Cursor::new(frames(&input)), w.clone(), &mut list, &fonts())?;
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
    while let Ok(Some((laid, l))) = clazel_gpu::channel::read_list(&mut rest) {
        // Laid out for the viewport the renderer was given, which is the kernel's.
        assert_eq!((laid.width, laid.height), (100, 40));
        let frames = server.list(laid, &l);
        assert!(frames.as_ref().is_ok_and(|f| f.len() == 1), "{frames:?}");
        frames_drawn.extend(frames.unwrap_or_default());
    }
    assert!(rest.is_empty());
    assert_eq!(frames_drawn.len(), 1);
    let first = frames_drawn.first().map(|f| f.pixels.clone());
    // The test's own draw, of a second run of the renderer over the same
    // input. Under Miri it draws the bytes the first run wrote instead: the
    // second run is another 71 s of Miri time there (parse, style, layout
    // and glyph masks; measured, 324 s with it and 252 s without), and what
    // Miri is here for is the GPU process's reader and the two draws, which
    // both still run.
    let own = if cfg!(miri) {
        sent_of(&w, &list)
    } else {
        run(&input)?
    };
    assert_eq!(first, Some(draw(&own, 100, 40)));
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

/// A click on a `javascript:` link sends no `Navigate`: the URL is the
/// page's to evaluate (item 7.15), and the kernel never sees it.
#[test]
fn javascript_links_are_not_navigations() -> Result<(), RunError> {
    let mut input = commit(
        "<!DOCTYPE html><body style='margin:0'><a href='JavaScript:alert(1)' style='display:block;height:20px'>js</a>",
        "text/html",
    );
    input.push(viewport(100, 50));
    input.push(Msg::Input {
        kind: 0,
        x: 5,
        y: 5,
        negative: false,
        delta: 0,
        key: 0,
    });
    let s = run(&input)?;
    assert!(
        !s.kernel.iter().any(|m| matches!(m, Msg::Navigate { .. })),
        "{:?}",
        s.kernel
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
#[cfg_attr(
    miri,
    ignore = "its one case, a layout of the whole fixture, takes about 47 minutes under Miri"
)]
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

// ---- The page's scripts (phase-7.md items 7.15 and 7.17) --------------------

use std::collections::VecDeque;
use std::io::Read;

use clazel_web::scripting::time::Clock;

use crate::run_graphics_with;

/// A clock the test moves.
#[derive(Clone, Default)]
struct TestClock(Arc<Mutex<u64>>);

impl Clock for TestClock {
    fn now_us(&mut self) -> u64 {
        self.0.lock().map_or(0, |v| *v)
    }
}

/// One thing the kernel's socket does: deliver bytes, or have nothing for
/// `ms` milliseconds (a read that times out, with the clock moving).
enum Step {
    Bytes(Vec<u8>),
    Idle(u64),
}

/// The kernel's socket, scripted.
struct Steps {
    queue: VecDeque<Step>,
    clock: TestClock,
}

impl Read for Steps {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self.queue.pop_front() {
            None => Ok(0),
            Some(Step::Idle(ms)) => {
                if let Ok(mut t) = self.clock.0.lock() {
                    *t = t.saturating_add(ms.saturating_mul(1000));
                }
                Err(std::io::Error::from(std::io::ErrorKind::TimedOut))
            }
            Some(Step::Bytes(mut bytes)) => {
                let n = bytes.len().min(buf.len());
                let rest = bytes.split_off(n);
                buf.get_mut(..n).unwrap_or_default().copy_from_slice(&bytes);
                if !rest.is_empty() {
                    self.queue.push_front(Step::Bytes(rest));
                }
                Ok(n)
            }
        }
    }
}

fn bytes(msgs: &[Msg]) -> Step {
    Step::Bytes(frames(msgs))
}

/// The frames the renderer wrote, as the kernel decodes them, and the lists
/// as the GPU process reads them.
fn sent_of(w: &Shared, list: &[u8]) -> Sent {
    let kernel = split_frames(&w.bytes())
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
    let mut raw = Vec::new();
    let mut rest = list;
    while let Ok(Some((_, l))) = clazel_gpu::channel::read_list(&mut rest) {
        raw.push(l);
    }
    assert!(rest.is_empty(), "bytes left after the last list");
    let lists = raw.iter().map(|b| decode(b).unwrap_or_default()).collect();
    Sent { kernel, lists, raw }
}

/// Runs the renderer over `steps` with a clock they move.
fn run_steps(steps: Vec<Step>) -> Result<Sent, RunError> {
    let clock = TestClock::default();
    let reader = Steps {
        queue: steps.into(),
        clock: clock.clone(),
    };
    let w = Shared::default();
    let mut list = Vec::new();
    run_graphics_with(reader, w.clone(), &mut list, &fonts(), &mut || {
        Box::new(clock.clone())
    })?;
    Ok(sent_of(&w, &list))
}

/// The pixels of list `n` alone, as `draw` makes them for all of them.
fn draw_one(s: &Sent, n: usize, width: u32, height: u32) -> Vec<u8> {
    let one = Sent {
        kernel: Vec::new(),
        lists: s.lists.get(n).cloned().into_iter().collect(),
        raw: s.raw.get(n).cloned().into_iter().collect(),
    };
    draw(&one, width, height)
}

const BLUE: [u8; 4] = [0, 0, 255, 255];
const GREEN: [u8; 4] = [0, 255, 0, 255];

/// The width of the viewport of the tests that draw a first frame and a
/// second and read the pixel at (5, 5) of each. Nothing they assert is to
/// the right of that pixel, and the software backend's time is in the
/// pixels: under Miri a 100 by 50 frame is 42 s of its time (measured:
/// `a_click_runs_the_handler_of_the_element_under_the_pointer` took 254 s
/// with no draw, 369 s with one draw of both frames and 440 s with the first
/// frame drawn alone as well).
const NARROW: u64 = 16;

/// The pixel at (5, 5) is `first` in the first list drawn alone and `last`
/// after every list, on a `NARROW` by `height` viewport.
///
/// Under Miri the first list is not also drawn alone: the draw of every
/// list draws it, through the same backend, before the others, so Miri
/// still interprets its drawing, and a second GPU with one more frame is
/// another 72 s of its time for a pixel the native run reads.
/// `a_script_changes_the_document_before_the_first_paint` and
/// `inline_styles_to_pixels` read a first frame's pixels there.
fn assert_frames(s: &Sent, height: u32, first: [u8; 4], last: [u8; 4]) {
    let width = u32::try_from(NARROW).unwrap_or(u32::MAX);
    if !cfg!(miri) {
        assert_eq!(pixel(&draw_one(s, 0, width, height), width, 5, 5), first);
    }
    assert_eq!(pixel(&draw(s, width, height), width, 5, 5), last);
}

/// A blue square, which a script turns green.
const SQUARE: &str = "<!DOCTYPE html><body style='margin:0'>\
<div id=d style='width:10px;height:10px;background:#0000ff'></div>";

/// The script that turns the square green.
const TURN_GREEN: &str = "document.getElementById('d').setAttribute('style', \
'width:10px;height:10px;background:#00ff00');";

/// The document is laid out and painted with what a script changed (the
/// script runs before the first paint).
#[test]
fn a_script_changes_the_document_before_the_first_paint() -> Result<(), RunError> {
    let html = format!("{SQUARE}<script>{TURN_GREEN}</script>");
    let mut input = commit(&html, "text/html");
    input.push(viewport(100, 40));
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 1);
    assert_eq!(pixel(&draw(&s, 100, 40), 100, 5, 5), GREEN);
    Ok(())
}

/// A timer changes the document later, and the page is styled, laid out and
/// painted again.
#[test]
fn a_timer_changes_the_document_and_the_page_is_painted_again() -> Result<(), RunError> {
    let html = format!("{SQUARE}<script>setTimeout(function () {{ {TURN_GREEN} }}, 50);</script>");
    let mut input = commit(&html, "text/html");
    input.push(viewport(NARROW, 40));
    let s = run_steps(vec![bytes(&input), Step::Idle(20), Step::Idle(40)])?;
    // Blue, then (after 60 ms on the page's clock) green.
    assert_eq!(s.lists.len(), 2);
    assert!(all_valid(&s));
    assert_frames(&s, 40, BLUE, GREEN);
    Ok(())
}

#[test]
fn a_timer_that_is_not_due_does_not_run() -> Result<(), RunError> {
    let html = format!("{SQUARE}<script>setTimeout(function () {{ {TURN_GREEN} }}, 500);</script>");
    let mut input = commit(&html, "text/html");
    input.push(viewport(100, 40));
    let s = run_steps(vec![bytes(&input), Step::Idle(20)])?;
    assert_eq!(s.lists.len(), 1);
    Ok(())
}

/// A title a script changes goes to the kernel.
#[test]
fn a_title_a_script_sets_goes_to_the_kernel() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><title>old</title><body>\
         <script>setTimeout(function () { document.querySelector('title')\
         .textContent = 'new'; }, 10);</script>";
    let mut input = commit(html, "text/html");
    input.push(viewport(100, 40));
    let s = run_steps(vec![bytes(&input), Step::Idle(20)])?;
    assert_eq!(
        s.kernel,
        vec![
            Msg::Title {
                title: b"old".to_vec()
            },
            Msg::Title {
                title: b"new".to_vec()
            }
        ]
    );
    Ok(())
}

/// A `javascript:` link the page drew runs in the page when it is clicked,
/// the kernel never sees a `Navigate` for it, and the page is painted again.
#[test]
fn a_clicked_javascript_link_runs_its_script() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body style='margin:0'>\
        <div id=d style='width:10px;height:10px;background:#0000ff'></div>\
        <a href=\"javascript:document.getElementById('d').setAttribute('style','width:10px;height:10px;background:%2300ff00')\" \
        style='display:block;height:20px'>go</a>";
    let mut input = commit(html, "text/html");
    input.push(viewport(NARROW, 50));
    input.push(Msg::Input {
        kind: 0,
        x: 5,
        y: 15,
        negative: false,
        delta: 0,
        key: 0,
    });
    let s = run(&input)?;
    assert!(
        !s.kernel.iter().any(|m| matches!(m, Msg::Navigate { .. })),
        "{:?}",
        s.kernel
    );
    assert_eq!(s.lists.len(), 2);
    assert_frames(&s, 50, BLUE, GREEN);
    Ok(())
}

/// A script that sets `location.href` makes the kernel's `Navigate`, and
/// `pushState` its `UpdateUrl`.
#[test]
fn navigation_and_history_are_the_kernels_messages() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body><script>\
        history.pushState(null, '', '/dir/two');\
        history.replaceState(null, '', '/dir/three');\
        location.href = '/next';</script>";
    let input = commit(html, "text/html");
    let s = run(&input)?;
    assert!(s.kernel.contains(&Msg::UpdateUrl {
        replace: false,
        url: b"http://a.example/dir/two".to_vec()
    }));
    assert!(s.kernel.contains(&Msg::UpdateUrl {
        replace: true,
        url: b"http://a.example/dir/three".to_vec()
    }));
    assert!(s.kernel.contains(&Msg::Navigate {
        url: b"http://a.example/next".to_vec()
    }));
    Ok(())
}

/// An external script is a `FetchScript`; the kernel's `ScriptResponse`,
/// `ScriptBody` and `ScriptEnd` give it to the page, which runs it and is
/// painted again; `ScriptFailed` is a network error.
#[test]
fn an_external_script_is_a_fetch_script() -> Result<(), RunError> {
    let html = format!("{SQUARE}<script src=/app.js></script><script src=/gone.js></script>");
    let mut input = commit(&html, "text/html");
    input.push(viewport(NARROW, 40));
    let answers = [
        Msg::ScriptResponse {
            request: 1,
            content_type: b"text/javascript".to_vec(),
        },
        Msg::ScriptBody {
            request: 1,
            bytes: b"document.getElementById('d').setAttribute('style',".to_vec(),
        },
        Msg::ScriptBody {
            request: 1,
            bytes: b"'width:10px;height:10px;background:#00ff00');".to_vec(),
        },
        Msg::ScriptEnd { request: 1 },
        Msg::ScriptFailed { request: 2 },
    ];
    let s = run_steps(vec![bytes(&input), bytes(&answers)])?;
    let fetches: Vec<&Msg> = s
        .kernel
        .iter()
        .filter(|m| matches!(m, Msg::FetchScript { .. }))
        .collect();
    // The second script is a parser-blocking one too: it is fetched when
    // the first has run, not before.
    assert_eq!(
        fetches,
        vec![
            &Msg::FetchScript {
                request: 1,
                url: b"http://a.example/app.js".to_vec()
            },
            &Msg::FetchScript {
                request: 2,
                url: b"http://a.example/gone.js".to_vec()
            }
        ]
    );
    assert_frames(&s, 40, BLUE, GREEN);
    Ok(())
}

/// `document.cookie` and `localStorage` wait for the kernel's answer in the
/// middle of the script, while the kernel's other messages (a `Viewport`
/// sent before the answer) wait their turn.
#[test]
fn a_script_waits_for_the_kernel_without_losing_its_other_messages() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body style='margin:0'>\
        <script>document.cookie = 'a=1'; var c = document.cookie;\
        localStorage.setItem('k', 'v');</script>";
    let mut input = commit(html, "text/html");
    // The answers come after a `Viewport`, which is read while they are
    // awaited.
    input.push(viewport(60, 30));
    input.push(Msg::CookieValue {
        cookie_string: b"a=1".to_vec(),
    });
    input.push(Msg::StorageLengthValue { length: 1 });
    let s = run(&input)?;
    assert!(s.kernel.contains(&Msg::CookieSet {
        cookie_string: b"a=1".to_vec()
    }));
    assert!(s.kernel.contains(&Msg::CookieGet));
    assert!(s.kernel.contains(&Msg::StorageSetItem {
        key: b"k".to_vec(),
        value: b"v".to_vec()
    }));
    // The `Viewport` was not lost: the page was laid out for it.
    assert_eq!(s.lists.len(), 1);
    Ok(())
}

// ---- Events and input (item 7.14) -----------------------------------------------

/// A 100 by 20 blue block that `onclick` turns green, at the top of a page
/// with a viewport 50 high.
const CLICKABLE: &str = "<!DOCTYPE html><body style='margin:0'>\
    <div id=d style='width:100px;height:20px;background:#0000ff' \
    onclick=\"this.setAttribute('style','width:100px;height:20px;background:#00ff00')\"></div>";

fn click_at(x: u64, y: u64) -> Msg {
    Msg::Input {
        kind: 0,
        x,
        y,
        negative: false,
        delta: 0,
        key: 0,
    }
}

fn key_msg(key: u64) -> Msg {
    Msg::Input {
        kind: 2,
        x: 0,
        y: 0,
        negative: false,
        delta: 0,
        key,
    }
}

/// The element under the pointer gets the click (hit-tested through the
/// layout), its `onclick` handler changes the document, and the page is
/// painted again. (A click on nothing is
/// `a_bare_canvas_click_runs_no_handler`: a page a test, each page being
/// minutes of Miri time.)
#[test]
fn a_click_runs_the_handler_of_the_element_under_the_pointer() -> Result<(), RunError> {
    let mut input = commit(CLICKABLE, "text/html");
    input.push(viewport(NARROW, 50));
    input.push(click_at(5, 5));
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 2);
    assert_frames(&s, 50, BLUE, GREEN);
    Ok(())
}

/// A click below the block, on the canvas, is not on the block: it reaches
/// the document element only, no handler runs and nothing is painted again.
///
/// The name sorts first among this module's tests on purpose. Miri runs
/// them on one thread in name order, and the first to lay out a page also
/// parses the user-agent style sheets for the process (66 s of Miri time,
/// measured: every page test is that much longer run alone). This is the
/// lightest page here (91 s), so that cost falls on it and not on a test
/// that is near the 300 s limit already.
#[test]
fn a_bare_canvas_click_runs_no_handler() -> Result<(), RunError> {
    let mut input = commit(CLICKABLE, "text/html");
    input.push(viewport(NARROW, 50));
    input.push(click_at(5, 40));
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 1, "a click below the block is not on it");
    Ok(())
}

/// A handler that returns false cancels the click: the link is not followed.
#[test]
fn a_canceled_click_is_not_a_navigation() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body style='margin:0'>\
        <a href='next' onclick='return false' style='display:block;height:20px'>go</a>\
        <a href='other' style='display:block;height:20px'>go</a>";
    let mut input = commit(html, "text/html");
    input.push(viewport(100, 50));
    input.push(click_at(5, 5));
    input.push(click_at(5, 25));
    let s = run(&input)?;
    let navigations: Vec<&Msg> = s
        .kernel
        .iter()
        .filter(|m| matches!(m, Msg::Navigate { .. }))
        .collect();
    assert_eq!(
        navigations,
        vec![&Msg::Navigate {
            url: b"http://a.example/dir/other".to_vec()
        }]
    );
    Ok(())
}

/// A click on a submit button submits its form: a `GET` is the kernel's
/// `Navigate` with the entry list in the query, a `POST` its `Submit`.
#[test]
fn a_click_on_a_submit_button_submits_the_form() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body style='margin:0'>\
        <form action='s'><input type=hidden name=q value='a b'>\
        <button name=go value=1 style='display:block;width:80px;height:20px'>Go</button></form>\
        <form method=post action='p'><input type=hidden name=q value=2>\
        <button style='display:block;width:80px;height:20px'>Post</button></form>";
    let mut input = commit(html, "text/html");
    input.push(viewport(100, 60));
    input.push(click_at(5, 5));
    input.push(click_at(5, 25));
    let s = run(&input)?;
    assert!(
        s.kernel.contains(&Msg::Navigate {
            url: b"http://a.example/dir/s?q=a+b&go=1".to_vec()
        }),
        "{:?}",
        s.kernel
    );
    assert!(
        s.kernel.contains(&Msg::Submit {
            url: b"http://a.example/dir/p".to_vec(),
            method: b"POST".to_vec(),
            content_type: b"application/x-www-form-urlencoded".to_vec(),
            body: b"q=2".to_vec(),
        }),
        "{:?}",
        s.kernel
    );
    Ok(())
}

/// A wheel input at (5, 5).
fn wheel_at_5_5(delta: u64) -> Msg {
    Msg::Input {
        kind: 1,
        x: 5,
        y: 5,
        negative: false,
        delta,
        key: 0,
    }
}

/// A page can cancel the wheel: its scroll then does not happen (no new
/// list). (With `a_scroll_is_an_event_and_its_change_is_painted` this was
/// one test of two pages; a page a test, each being minutes of Miri time.)
#[test]
fn a_canceled_wheel_does_not_scroll() -> Result<(), RunError> {
    let canceled = "<!DOCTYPE html><body style='margin:0'>\
        <div onwheel='return false' style='height:500px;background:#0000ff'></div>";
    let mut input = commit(canceled, "text/html");
    input.push(viewport(10, 50));
    input.push(wheel_at_5_5(100));
    let s = run(&input)?;
    // The handler ran, so the page was painted again (it could have changed
    // something), but not scrolled: the same list.
    assert!(s.lists.len() <= 2);
    assert_eq!(s.lists.first(), s.lists.last(), "canceled: no scroll");
    Ok(())
}

/// A `scroll` listener runs when the wheel scrolls the page, and its change
/// is painted.
#[test]
fn a_scroll_is_an_event_and_its_change_is_painted() -> Result<(), RunError> {
    let scrolled = "<!DOCTYPE html><body style='margin:0' \
        onscroll=\"document.getElementById('m').setAttribute('style','height:500px;background:#00ff00')\">\
        <div id=m style='height:500px;background:#0000ff'></div>";
    let mut input = commit(scrolled, "text/html");
    input.push(viewport(10, 50));
    input.push(wheel_at_5_5(100));
    let s = run(&input)?;
    // The first paint, then the scroll (with the handler's change) painted
    // once.
    assert_eq!(s.lists.len(), 2, "the scroll painted once");
    Ok(())
}

/// Tab focuses the first input and a typed character goes into it: the
/// page's `oninput` runs and its change is painted.
#[test]
fn keys_reach_the_focused_input() -> Result<(), RunError> {
    let html = "<!DOCTYPE html><body style='margin:0'>\
        <input id=i oninput=\"document.getElementById('d').setAttribute('style','width:100px;height:20px;background:#00ff00')\">\
        <div id=d style='width:100px;height:20px;background:#0000ff'></div>";
    let mut input = commit(html, "text/html");
    input.push(viewport(100, 50));
    input.push(key_msg(9));
    input.push(key_msg(u64::from(b'a')));
    let s = run(&input)?;
    assert_eq!(s.lists.len(), 2);
    Ok(())
}
