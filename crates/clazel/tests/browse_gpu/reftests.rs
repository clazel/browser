//! The reftest runner (`tests/reftest/`, phase-5.md item 5.25) with
//! `clazel browse --headless` as its renderer: each page is served by the
//! in-process server under its WPT path, and `browse --headless` (the host,
//! the kernel, the real renderer and the real GPU process) writes an
//! 800×600 PNG of it at scale 1, which is decoded and compared.
//!
//! - A pair of pages written here checks the plumbing: a match that
//!   passes, a mismatch that passes, and a match that fails.
//! - The WPT reftests this repository vendors that are in the subset
//!   (`clazel-style/tests/data/wpt-mediaqueries/`) are run and counted:
//!   pass, fail, not run by reason, error. Nothing asserts the counts (the
//!   PR body reports them); the test fails only if the runner did not run
//!   every page.
//!
//! A module of `browse_gpu.rs`, and so macOS on Apple silicon only.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Arc, Mutex};

use crate::gpu::{Fixture, fixture};
use crate::picture::check::decode_png;
use crate::reftest::pixels::Image;
use crate::reftest::runner::{Outcome, Render, run};
use crate::server::{Reply, Request, Server, serve};

/// The pages being served: WPT path (no leading `/`) to bytes.
type Pages = Arc<Mutex<HashMap<String, Vec<u8>>>>;

/// `browse --headless` against the in-process server.
struct Headless {
    clazel: PathBuf,
    renderer: PathBuf,
    gpu: PathBuf,
    out: PathBuf,
    pages: Pages,
    server: Server,
}

/// WPT's server's content type for a file (by its extension).
fn content_type(path: &str) -> &'static str {
    if path.ends_with(".xht") || path.ends_with(".xhtml") {
        "application/xhtml+xml"
    } else if path.ends_with(".css") {
        "text/css"
    } else {
        "text/html"
    }
}

impl Headless {
    fn new(f: &Fixture) -> Self {
        let pages: Pages = Arc::default();
        let shared = Arc::clone(&pages);
        let server = serve(move |r: &Request| {
            let path = r.path.trim_start_matches('/').to_owned();
            let page = shared.lock().ok().and_then(|p| p.get(&path).cloned());
            match page {
                Some(bytes) => Reply {
                    head: format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: {}\r\n",
                        content_type(&path)
                    ),
                    piece: bytes,
                    times: 1,
                },
                None => Reply {
                    head: "HTTP/1.1 404 Not Found\r\nContent-Type: text/plain\r\n".to_owned(),
                    piece: b"not found".to_vec(),
                    times: 1,
                },
            }
        });
        Headless {
            clazel: f.clazel.clone(),
            renderer: f.renderer.clone(),
            gpu: f.gpu.clone(),
            out: f.dir.join("reftest.png"),
            pages,
            server,
        }
    }
}

impl Render for Headless {
    fn render(&mut self, path: &str, bytes: &[u8]) -> Result<Image, String> {
        let path = path.trim_start_matches('/');
        if let Ok(mut p) = self.pages.lock() {
            p.insert(path.to_owned(), bytes.to_vec());
        }
        let _ = std::fs::remove_file(&self.out);
        let url = format!("http://{}/{path}", self.server.addr);
        let ran = crate::gpu::output(
            Command::new(&self.clazel)
                .args(["--headless"])
                .arg(&self.out)
                .args(["--size", "800x600", &url])
                .env("CLAZEL_RENDERER", &self.renderer)
                .env("CLAZEL_GPU", &self.gpu),
        )
        .map_err(|e| format!("{path}: browse: {e}"))?;
        if !ran.status.success() {
            let err = String::from_utf8_lossy(&ran.stderr);
            let last = err.lines().last().unwrap_or("").to_owned();
            return Err(format!("{path}: browse --headless: {}: {last}", ran.status));
        }
        let file = std::fs::read(&self.out).map_err(|e| format!("{path}: {e}"))?;
        // `browse --headless` writes RGB; the runner's images are RGBA.
        let (width, height, rgb) = decode_png(&file).ok_or(format!("{path}: not a PNG"))?;
        let rgba = rgb
            .as_chunks::<3>()
            .0
            .iter()
            .flat_map(|&[r, g, b]| [r, g, b, 255])
            .collect();
        Ok(Image {
            width,
            height,
            rgba,
        })
    }
}

/// A file reader over `files` (WPT paths to bytes).
fn reader(files: HashMap<String, Vec<u8>>) -> impl Fn(&str) -> Option<Vec<u8>> {
    move |p: &str| files.get(p.trim_start_matches('/')).cloned()
}

/// A green 100 px square, three ways, and a red one.
const SQUARE_DIV: &str = "<!doctype html><link rel=match href=ref-border.html>\
<link rel=mismatch href=ref-red.html>\
<body style='margin:0;background:#ffffff'>\
<div style='width:100px;height:100px;background:#008000'></div>";
const SQUARE_BORDER: &str = "<!doctype html><body style='margin:0;background:#ffffff'>\
<div style='width:0;height:0;border:50px solid #008000'></div>";
const SQUARE_RED: &str = "<!doctype html><body style='margin:0;background:#ffffff'>\
<div style='width:100px;height:100px;background:#ff0000'></div>";
const MATCHES_RED: &str = "<!doctype html><link rel=match href=ref-red.html>\
<body style='margin:0;background:#ffffff'>\
<div style='width:100px;height:100px;background:#008000'></div>";

#[test]
#[cfg_attr(miri, ignore)]
fn browse_headless_renders_reftests() {
    if !crate::runs() {
        return;
    }
    let f = fixture("reftest-plumbing");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let mut headless = Headless::new(&f);
    let files: HashMap<String, Vec<u8>> = [
        ("t/square.html", SQUARE_DIV),
        ("t/ref-border.html", SQUARE_BORDER),
        ("t/ref-red.html", SQUARE_RED),
        ("t/matches-red.html", MATCHES_RED),
    ]
    .into_iter()
    .map(|(p, s)| (p.to_owned(), s.as_bytes().to_vec()))
    .collect();
    let read = reader(files);
    assert_eq!(run("t/square.html", &read, &mut headless), Outcome::Pass);
    let failed = run("t/matches-red.html", &read, &mut headless);
    assert!(
        matches!(
            &failed,
            Outcome::Fail {
                difference: Some((_, 10_000)),
                ..
            }
        ),
        "{failed:?}"
    );
}

/// Where the vendored media queries reftests are, and their WPT directory.
const MEDIAQUERIES: (&str, &str) = (
    concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clazel-style/tests/data/wpt-mediaqueries"
    ),
    "css/mediaqueries",
);

/// The vendored references, laid out by their WPT paths (`README.md` there).
const REFERENCES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/wpt-references");

/// Every file under `dir`, keyed by its path below `root`.
fn tree(root: &std::path::Path, dir: &std::path::Path, into: &mut HashMap<String, Vec<u8>>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            tree(root, &path, into);
        } else if let (Ok(rel), Ok(bytes)) = (path.strip_prefix(root), std::fs::read(&path)) {
            into.insert(rel.to_string_lossy().into_owned(), bytes);
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn the_vendored_wpt_reftests_are_run_and_counted() {
    if !crate::runs() {
        return;
    }
    let f = fixture("reftest-wpt");
    assert!(f.is_ok(), "{:?}", f.as_ref().err());
    let Ok(f) = f else { return };
    let (dir, wpt) = MEDIAQUERIES;
    let mut files = HashMap::new();
    let mut tests = Vec::new();
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(bytes) = std::fs::read(entry.path()) else {
            continue;
        };
        let path = format!("{wpt}/{name}");
        let reftest = (name.ends_with(".html") || name.ends_with(".xht"))
            && (bytes.windows(9).any(|w| w == b"rel=\"matc")
                || bytes.windows(9).any(|w| w == b"rel=\"mism")
                || bytes.windows(9).any(|w| w == b"rel=match"));
        if reftest {
            tests.push(path.clone());
        }
        files.insert(path, bytes);
    }
    tests.sort();
    let root = std::path::Path::new(REFERENCES);
    tree(root, &root.join("css"), &mut files);
    // Every reference the tests name is vendored, so none is "missing".
    for t in &tests {
        let meta = files.get(t).map(|b| crate::reftest::meta::read(t, b));
        assert!(
            matches!(meta, Some(Ok(_))),
            "{t}: its metadata does not read"
        );
        let Some(Ok(meta)) = meta else { return };
        for r in &meta.references {
            assert!(
                files.contains_key(&r.path),
                "{t}: {} is not vendored",
                r.path
            );
        }
    }
    let read = reader(files);
    let mut headless = Headless::new(&f);
    let mut tally: HashMap<String, Vec<String>> = HashMap::new();
    for t in &tests {
        let outcome = run(t, &read, &mut headless);
        let key = match &outcome {
            Outcome::Pass => "pass".to_owned(),
            Outcome::Fail { .. } => "fail".to_owned(),
            Outcome::NotRun(why) => format!("not run: {why:?}"),
            Outcome::NotAReftest => "not a reftest".to_owned(),
            Outcome::Error(e) => format!("error: {e}"),
        };
        eprintln!("reftest {t}: {outcome:?}");
        tally.entry(key).or_default().push(t.clone());
    }
    let mut keys: Vec<_> = tally.iter().collect();
    keys.sort();
    for (k, v) in keys {
        eprintln!("reftests: {} {k}", v.len());
    }
    let counted: usize = tally.values().map(Vec::len).sum();
    assert_eq!(counted, tests.len());
    assert!(!tests.is_empty(), "no vendored reftests found in {dir}");
}
