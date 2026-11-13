//! Linked style sheets through real processes (phase-5.md items 5.19, 5.20
//! and 5.26's third bullet, as far as it goes on macOS): the host, the proven
//! kernel, the real sandboxed renderer and the real GPU process, against an
//! in-process server that records what it was asked.
//!
//! - A page whose only styling is in its linked sheet is painted with the
//!   sheet's rules (pixels only the sheet produces).
//! - The sheet request carries the page's cookie when it is same-origin and
//!   none when it is cross-origin (the server records each request's head).
//! - A sheet that never answers is failed by the kernel's timeout (the host's
//!   clock is moved past it), and the page is painted without it.
//! - The HN-shaped fixture (`tests/fixtures/hn/`) is served with its sheet,
//!   which is requested and changes the page.
//!
//! A module of `browse_gpu.rs` (so its support is shared without unused
//! items), and so macOS on Apple silicon only.

use std::process::Command;
use std::time::{Duration, Instant};

use crate::gpu::{self, Fixture, fixture, metal, painted};
use crate::server::{self, Reply, Request, field, serve};
use clazel::Host;
use clazel_kernel::exec::records::EventRecord;

const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

fn runs() -> bool {
    match metal() {
        Ok(()) => true,
        Err(why) => {
            eprintln!("clazel sheets: skipped: no Metal device ({why})");
            assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
            false
        }
    }
}

/// A host with the real renderer and the real GPU process, every connection
/// routed to `server`, its clock fixed at `clock` (seconds since 1601).
fn host(f: &Fixture, server: &server::Server, clock: u64) -> Host {
    let (renderer, gpu) = (f.renderer.clone(), f.gpu.clone());
    let mut host = Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--font", DEJAVU]);
        c
    })
    .with_gpu(move |_| Command::new(&gpu));
    host.route = Some(server.addr);
    host.clock = Some(clock);
    host
}

/// A tab at `url`, sized `w` by `h` at scale 1.
fn open(host: &mut Host, url: &str, (w, h): (u64, u64)) -> u64 {
    let tab = host.open(url);
    host.event(EventRecord::Resize {
        tab,
        width: w,
        height: h,
        scale: 1,
    });
    tab
}

fn pixel(p: &gpu::Painted, x: u32, y: u32) -> Option<[u8; 4]> {
    let i = usize::try_from(
        y.checked_mul(p.frame.width)?
            .checked_add(x)?
            .checked_mul(4)?,
    )
    .ok()?;
    p.frame.pixels.get(i..i.checked_add(4)?)?.try_into().ok()
}

fn reply(content_type: &str, extra: &str, body: &str) -> Reply {
    Reply {
        head: format!("HTTP/1.1 200 OK\r\nContent-Type: {content_type}\r\n{extra}"),
        piece: body.as_bytes().to_vec(),
        times: 1,
    }
}

/// 2026-11-13 in seconds since 1601 (any fixed time will do).
const NOW: u64 = 13_409_078_400;

/// The page: green only if its same-origin sheet applies, and a
/// cross-origin sheet that would make a second band blue. It sets a cookie.
const PAGE: &str = "<!doctype html><title>Sheets</title>\
<link rel=stylesheet href='/same.css'>\
<link rel=stylesheet href='http://other.test/cross.css'>\
<body style='margin:0;background:#ffffff'><div class=a></div><div class=b></div></body>";

#[test]
#[cfg_attr(miri, ignore)]
fn linked_sheets_apply_with_the_cookie_only_same_origin() {
    if !runs() {
        return;
    }
    let f = fixture("sheets-apply");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let server = serve(|r: &Request| match r.path.as_str() {
        "/same.css" => reply("text/css", "", ".a { height: 20px; background: #00ff00 }"),
        "/cross.css" => reply("text/css", "", ".b { height: 20px; background: #0000ff }"),
        _ => reply("text/html", "Set-Cookie: sid=s3cret; Path=/\r\n", PAGE),
    });
    let mut host = host(&f, &server, NOW);
    let tab = open(&mut host, "http://pages.test/", (100, 60));
    let p = painted(&mut host, tab);
    assert!(p.is_some(), "no paint:\n{}", host.log.join("\n"));
    let Some(p) = p else { return };
    assert_eq!(
        pixel(&p, 50, 10),
        Some([0, 255, 0, 255]),
        "the same-origin sheet's rule"
    );
    assert_eq!(
        pixel(&p, 50, 30),
        Some([0, 0, 255, 255]),
        "the cross-origin sheet's rule"
    );
    let seen = server.seen.lock().map(|s| s.clone()).unwrap_or_default();
    let get = |path: &str| seen.iter().find(|r| r.path == path).cloned();
    let same = get("/same.css");
    let cross = get("/cross.css");
    assert_eq!(same.as_ref().map(|r| r.host.as_str()), Some("pages.test"));
    assert_eq!(cross.as_ref().map(|r| r.host.as_str()), Some("other.test"));
    assert_eq!(
        same.map(|r| field(&r.head, "cookie")).as_deref(),
        Some("sid=s3cret")
    );
    assert_eq!(cross.map(|r| field(&r.head, "cookie")).as_deref(), Some(""));
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_sheet_that_never_answers_times_out_and_the_page_renders() {
    if !runs() {
        return;
    }
    let f = fixture("sheets-timeout");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let server = serve(|r: &Request| {
        if r.path == "/hang.css" {
            // Never answer within the test (the thread is left behind).
            std::thread::sleep(Duration::from_secs(600));
        }
        reply(
            "text/html",
            "",
            "<!doctype html><link rel=stylesheet href='/hang.css'>\
             <body style='margin:0;background:#ff0000'>",
        )
    });
    let mut host = host(&f, &server, NOW);
    let tab = open(&mut host, "http://pages.test/", (40, 20));
    // Until the renderer has asked for the sheet: render-blocking, so no Paint.
    let end = Instant::now().checked_add(Duration::from_secs(20));
    while end.is_some_and(|e| Instant::now() < e)
        && !host
            .log
            .iter()
            .any(|l| l.contains("FetchStyle") || l.contains("fetch style"))
    {
        host.pump(Duration::from_millis(20));
    }
    let asked = host
        .log
        .iter()
        .any(|l| l.contains("FetchStyle") || l.contains("fetch style"));
    assert!(
        asked,
        "the renderer never asked for the sheet:\n{}",
        host.log.join("\n")
    );
    assert!(host.shown.is_empty(), "painted before the sheet ended");
    // The kernel's timeout is 60 s: move its clock past it.
    host.clock = Some(NOW + 61);
    host.event(EventRecord::Tick { time: NOW + 61 });
    let p = painted(&mut host, tab);
    assert!(
        p.is_some(),
        "no paint after the timeout:\n{}",
        host.log.join("\n")
    );
    assert_eq!(p.and_then(|p| pixel(&p, 20, 10)), Some([255, 0, 0, 255]));
}

#[test]
#[cfg_attr(miri, ignore)]
fn the_hn_shaped_fixture_is_served_with_its_sheet() {
    if !runs() {
        return;
    }
    let f = fixture("sheets-fixture");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let html = include_str!("../fixtures/hn/index.html");
    let css = include_str!("../fixtures/hn/site.css");
    let paint = |with_sheet: bool| -> Option<Vec<u8>> {
        let server = serve(move |r: &Request| {
            if r.path.starts_with("/site.css") {
                if with_sheet {
                    reply("text/css", "", css)
                } else {
                    Reply {
                        head: "HTTP/1.1 404 Not Found\r\nContent-Type: text/html\r\n".to_owned(),
                        piece: b"gone".to_vec(),
                        times: 1,
                    }
                }
            } else {
                reply("text/html", "", html)
            }
        });
        let mut host = host(&f, &server, NOW);
        let tab = open(&mut host, "http://fixture.test/", (800, 600));
        let p = painted(&mut host, tab)?;
        let asked = server
            .seen
            .lock()
            .is_ok_and(|s| s.iter().any(|r| r.path == "/site.css?v=7"));
        asked.then_some(p.frame.pixels)
    };
    let with = paint(true);
    let without = paint(false);
    assert!(
        with.is_some() && without.is_some(),
        "no paint, or the sheet was not asked for"
    );
    assert_ne!(with, without, "the sheet changed nothing");
}
