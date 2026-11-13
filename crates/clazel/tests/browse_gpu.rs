//! Phase-5.md item 5.23 through real processes, before the renderer draws (5.20):
//! a stand-in renderer (`support/gpu.rs`) writes a hand-built display list to the
//! list socket it inherits; the real GPU process (`clazel-gpu`, in its 5.21a
//! sandbox, on Metal) draws it; the kernel turns its `FrameReady` into a `Paint`
//! under the kernel's URL; and `clazel browse --headless` writes the frame as a
//! PNG and a PPM. Every image is compared with `clazel-gpu`'s software reference
//! for the list, within one level per channel. `browse_window.rs` shows the same
//! frame in a window.
//!
//! Then the whole pipeline with the real renderer (item 5.20) against an
//! in-process server: a page with inline styles is painted at its viewport,
//! painted again for a new viewport and for scrolls, a click on its link
//! navigates and paints the next page; and `browse --headless` writes a real
//! page's PNG, checked for its size, its background and some ink where its text
//! is.
//!
//! macOS on Apple silicon only (the GPU process's only backend). Without a Metal
//! device the tests say so and pass, except under CI, as `clazel-gpu`'s tests.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/gpu.rs"]
mod gpu;
#[path = "../cli/picture.rs"]
mod picture;
#[path = "support/server.rs"]
mod server;

use std::process::Command;

use clazel::Host;
use clazel_kernel::exec::records::EventRecord;
use gpu::{Fixture, close, fixture, host, metal, open, painted, reference};
use picture::check::decode_png;
use server::{Reply, Request, field, serve};

/// Whether to run: a Metal device, or fail under CI.
fn runs() -> bool {
    match metal() {
        Ok(()) => true,
        Err(why) => {
            eprintln!("clazel browse_gpu: skipped: no Metal device ({why})");
            assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
            false
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_hand_built_list_reaches_a_paint_under_the_kernels_url() {
    if !runs() {
        return;
    }
    let f = fixture("browse-gpu-paint");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let mut host = host(&f);
    let tab = open(&mut host, "http://gpu.test/", (80, 60));
    let got = painted(&mut host, tab);
    assert!(
        got.is_some(),
        "no Paint with its pixels; the host's log:\n{}",
        host.log.join("\n")
    );
    let Some(p) = got else { return };
    assert_eq!(p.url, "http://gpu.test/");
    assert_eq!((p.buffer, p.size), (0, (80, 60)));
    assert_eq!((p.frame.slot, p.frame.width, p.frame.height), (0, 80, 60));
    let want = reference(80, 60);
    assert!(
        want.as_deref().is_some_and(|w| close(&p.frame.pixels, w)),
        "the pixels differ from the reference"
    );
    drop(host);
}

/// `clazel browse --headless OUT URL` against a served page, with the stand-in
/// renderer and the real GPU process: `kind` is `png` or `ppm`.
fn headless(kind: &str) {
    if !runs() {
        return;
    }
    let f = fixture(&format!("browse-gpu-{kind}"));
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let server = serve(|r: &Request| {
        // The kernel asks for the page at its path, naming the server's host.
        assert_eq!(r.path, "/");
        assert_eq!(field(&r.head, "Host"), r.host);
        Reply {
            head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
            piece: b"<!doctype html><title>t</title>".to_vec(),
            times: 1,
        }
    });
    let out = f.dir.join(format!("out.{kind}"));
    let url = format!("http://{}/", server.addr);
    let ran = Command::new(&f.clazel)
        .args(["browse", "--headless"])
        .arg(&out)
        .args(["--size", "64x48", &url])
        .env("CLAZEL_RENDERER", &f.script)
        .env("CLAZEL_GPU", &f.gpu)
        .env("CLAZEL_TEST_LIST", &f.list)
        .output();
    let ok = ran.as_ref().is_ok_and(|o| o.status.success());
    let log = ran.map(|o| String::from_utf8_lossy(&o.stderr).into_owned());
    assert!(ok, "browse --headless failed: {log:?}");
    assert!(
        server.seen.lock().is_ok_and(|s| !s.is_empty()),
        "the page was never fetched"
    );
    let bytes = std::fs::read(&out).unwrap_or_default();
    let rgb = if kind == "png" {
        let decoded = decode_png(&bytes);
        assert!(
            decoded
                .as_ref()
                .is_some_and(|(w, h, _)| (*w, *h) == (64, 48))
        );
        let rgb = decoded.map(|(_, _, rgb)| rgb).unwrap_or_default();
        // The file is exactly what the writer makes of its own pixels.
        assert_eq!(picture::png(64, 48, &rgb), Some(bytes));
        rgb
    } else {
        let rgb = bytes
            .strip_prefix(&b"P6\n64 48\n255\n"[..])
            .map(<[u8]>::to_vec)
            .unwrap_or_default();
        assert_eq!(picture::ppm(64, 48, &rgb), Some(bytes));
        rgb
    };
    let want = reference(64, 48).map(|p| picture::rgb_over_white(&p));
    assert!(
        want.as_deref().is_some_and(|w| close(&rgb, w)),
        "the {kind} differs from the reference"
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn headless_writes_a_png() {
    headless("png");
}

#[test]
#[cfg_attr(miri, ignore)]
fn headless_writes_a_ppm() {
    headless("ppm");
}

/// The faces the real renderer lays out in: DejaVu Serif, vendored for
/// `clazel-font`'s tests, so the layout does not depend on the machine.
const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

/// The first page: a 40 px green link block at the top, a 300 px red block
/// below it, white text, and enough height to scroll.
const ONE: &str = "<!doctype html><title>One</title>\
<body style='margin:0;background:#2050c0'>\
<a href='/two' style='display:block;height:40px;background:#00ff00'>next</a>\
<div style='height:300px;background:#ff0000'></div>\
<p style='color:#ffffff'>Hello</p><div style='height:1000px'></div></body>";

/// The page the link leads to: yellow.
const TWO: &str = "<!doctype html><title>Two</title>\
<body style='margin:0;background:#ffff00'><p>two</p></body>";

fn pages() -> server::Server {
    serve(|r: &Request| Reply {
        head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
        piece: if r.path == "/two" { TWO } else { ONE }.as_bytes().to_vec(),
        times: 1,
    })
}

/// A host with the real renderer and the real GPU process.
fn real_host(f: &Fixture) -> Host {
    let (renderer, gpu) = (f.renderer.clone(), f.gpu.clone());
    Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--font", DEJAVU]);
        c
    })
    .with_gpu(move |_| Command::new(&gpu))
}

/// The RGBA of pixel (`x`, `y`) of `p`'s frame.
fn pixel(p: &gpu::Painted, x: u32, y: u32) -> Option<[u8; 4]> {
    let i = usize::try_from(
        y.checked_mul(p.frame.width)?
            .checked_add(x)?
            .checked_mul(4)?,
    )
    .ok()?;
    p.frame.pixels.get(i..i.checked_add(4)?)?.try_into().ok()
}

const GREEN: [u8; 4] = [0, 255, 0, 255];
const RED: [u8; 4] = [255, 0, 0, 255];
const YELLOW: [u8; 4] = [255, 255, 0, 255];

fn input(host: &mut Host, tab: u64, kind: u64, (x, y): (u64, u64), delta: i64) {
    host.event(EventRecord::Input {
        tab,
        kind,
        x,
        y,
        negative: delta < 0,
        delta: delta.unsigned_abs(),
        key: 0,
    });
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_real_page_repaints_for_viewports_and_scrolls_and_follows_a_click() {
    if !runs() {
        return;
    }
    let f = fixture("browse-pipeline");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let server = pages();
    let mut host = real_host(&f);
    host.route = Some(server.addr);
    let tab = host.open("http://pages.test/");
    let resize = |host: &mut Host, w: u64, h: u64| {
        host.event(EventRecord::Resize {
            tab,
            width: w,
            height: h,
            scale: 1,
        });
    };
    resize(&mut host, 200, 100);
    let log = |host: &Host| host.log.join("\n");
    let p = painted(&mut host, tab);
    assert!(p.is_some(), "no first paint:\n{}", log(&host));
    let Some(p) = p else { return };
    assert_eq!((p.url.as_str(), p.size), ("http://pages.test/", (200, 100)));
    assert_eq!(pixel(&p, 150, 5), Some(GREEN), "the link block");
    assert_eq!(pixel(&p, 150, 60), Some(RED), "the red block");

    // A new viewport lays out and paints again, at its size.
    resize(&mut host, 240, 120);
    let p = painted(&mut host, tab);
    assert!(
        p.as_ref().is_some_and(|p| p.size == (240, 120)),
        "no repaint at 240 by 120:\n{}",
        log(&host)
    );

    // A scroll of 60 pixels down moves the red block to the top; back up, the
    // link is there again.
    input(&mut host, tab, 1, (0, 0), 60);
    let p = painted(&mut host, tab);
    assert!(
        p.as_ref().is_some_and(|p| pixel(p, 150, 5) == Some(RED)),
        "no scrolled repaint:\n{}",
        log(&host)
    );
    input(&mut host, tab, 1, (0, 0), -60);
    let p = painted(&mut host, tab);
    assert!(
        p.as_ref().is_some_and(|p| pixel(p, 150, 5) == Some(GREEN)),
        "no repaint scrolled back"
    );

    // A click on the link: the renderer's `Navigate`, the kernel's fetch, the
    // next page painted under its URL.
    input(&mut host, tab, 0, (20, 10), 0);
    let p = painted(&mut host, tab);
    assert!(p.is_some(), "no paint after the click:\n{}", log(&host));
    let Some(p) = p else { return };
    assert_eq!(p.url, "http://pages.test/two");
    assert_eq!(pixel(&p, 150, 60), Some(YELLOW));
    let paths: Vec<String> = server
        .seen
        .lock()
        .map(|s| s.iter().map(|r| r.path.clone()).collect())
        .unwrap_or_default();
    assert_eq!(paths, ["/", "/two"]);
}

#[test]
#[cfg_attr(miri, ignore)]
fn headless_writes_a_real_pages_png() {
    if !runs() {
        return;
    }
    let f = fixture("browse-pipeline-png");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let server = serve(|_: &Request| Reply {
        head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
        piece: b"<!doctype html><title>t</title><body style='margin:0;background:#2050c0'>\
<p style='color:#ffffff;margin:8px'>Hello, world</p></body>"
            .to_vec(),
        times: 1,
    });
    let out = f.dir.join("page.png");
    let ran = Command::new(&f.clazel)
        .args(["browse", "--headless"])
        .arg(&out)
        .args(["--size", "200x120", &format!("http://{}/", server.addr)])
        .env("CLAZEL_RENDERER", &f.renderer)
        .env("CLAZEL_GPU", &f.gpu)
        .output();
    let ok = ran.as_ref().is_ok_and(|o| o.status.success());
    assert!(
        ok,
        "{:?}",
        ran.map(|o| String::from_utf8_lossy(&o.stderr).into_owned())
    );
    let decoded = decode_png(&std::fs::read(&out).unwrap_or_default());
    assert!(
        decoded
            .as_ref()
            .is_some_and(|(w, h, _)| (*w, *h) == (200, 120))
    );
    let rgb = decoded.map(|(_, _, rgb)| rgb).unwrap_or_default();
    let px: Vec<[u8; 3]> = rgb.as_chunks::<3>().0.to_vec();
    let background = px.iter().filter(|p| **p == [0x20, 0x50, 0xc0]).count();
    let ink = px.iter().filter(|p| p.iter().all(|c| *c > 0xc0)).count();
    assert!(
        background > 200 * 120 * 3 / 4,
        "{background} background pixels"
    );
    // The text is white in the top 40 rows (8 px margin, one line), and nowhere below.
    assert!(ink > 20, "{ink} white pixels");
    let ink_below = px
        .iter()
        .skip(200 * 40)
        .filter(|p| p.iter().all(|c| *c > 0xc0))
        .count();
    assert_eq!(ink_below, 0);
}
