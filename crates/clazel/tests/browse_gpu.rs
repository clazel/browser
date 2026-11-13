//! Phase-5.md item 5.23 through real processes, before the renderer draws (5.20):
//! a stand-in renderer (`support/gpu.rs`) writes a hand-built display list to the
//! list socket it inherits; the real GPU process (`clazel-gpu`, in its 5.21a
//! sandbox, on Metal) draws it; the kernel turns its `FrameReady` into a `Paint`
//! under the kernel's URL; and `clazel browse --headless` writes the frame as a
//! PNG and a PPM. Every image is compared with `clazel-gpu`'s software reference
//! for the list, within one level per channel. `browse_window.rs` shows the same
//! frame in a window.
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

use gpu::{close, fixture, host, metal, open, painted, reference};
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
